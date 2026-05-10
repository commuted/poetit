import json
import os
import re
import tempfile
import threading
import tkinter as tk
import tkinter.ttk as ttk
from tkinter import filedialog, messagebox
import tkinter.font as tkfont
import nltk
from nltk import word_tokenize
from nltk.corpus import words
from nltk.corpus import cmudict
from nltk.corpus import wordnet as wn
from nltk.tokenize import SyllableTokenizer

try:
    import prosodic as _prosodic
    _PROSODIC_AVAILABLE = True
except ImportError:
    _PROSODIC_AVAILABLE = False

try:
    import spacy as _spacy
    from spacy import displacy as _displacy
    _SPACY_AVAILABLE = True
except ImportError:
    _SPACY_AVAILABLE = False

try:
    import cairosvg as _cairosvg
    from PIL import Image as _PILImage, ImageTk as _PILImageTk
    import io as _io
    _DIAGRAM_AVAILABLE = True
except ImportError:
    _DIAGRAM_AVAILABLE = False

try:
    from dulwich.repo import Repo
    from dulwich.objects import Blob
    from dulwich import porcelain as _porcelain
    import dulwich.errors as _dulwich_errors
    _VCS_AVAILABLE = True
except ImportError:
    _VCS_AVAILABLE = False

# State file for persisting last-used repository
_STATE_DIR = os.path.join(os.path.expanduser("~"), ".poetit")
_STATE_FILE = os.path.join(_STATE_DIR, "state.json")

# spaCy dependency labels that reliably indicate prosodically weak words.
_WEAK_DEPS = frozenset({
    'aux',     # auxiliary verb:        shall, will, have, be
    'auxpass', # passive auxiliary:     was (seen)
    'det',     # determiner:            the, a, an, this
    'mark',    # subordinating conj.:   that, if, because
    'cc',      # coordinating conj.:    and, or, but
    'case',    # case marker:           's, of
    'expl',    # expletive:             there (is)
    'prep',    # preposition — most are weak in English
})

def _read_data(filename):
    """Return the text of a bundled data file.

    Tries importlib.resources first (works when installed via pip), then falls
    back to a path relative to this file (works in an editable install or when
    running app.py directly from the source tree).
    """
    from importlib.resources import files
    try:
        return files('poetit').joinpath('data', filename).read_text(encoding='utf-8')
    except Exception:
        pass
    here = os.path.dirname(os.path.abspath(__file__))
    candidate = os.path.join(here, 'data', filename)
    if os.path.exists(candidate):
        with open(candidate, encoding='utf-8') as fh:
            return fh.read()
    return None


_NLTK_PACKAGES = [
    ("tokenizers/punkt", "punkt_tab"),
    ("corpora/words", "words"),
    ("corpora/cmudict", "cmudict"),
    ("corpora/wordnet", "wordnet"),
    ("taggers/averaged_perceptron_tagger", "averaged_perceptron_tagger"),
    ("taggers/averaged_perceptron_tagger_eng", "averaged_perceptron_tagger_eng"),
]


def _ensure_nltk_data():
    """Download required NLTK data only if missing; swallow network errors."""
    for path, name in _NLTK_PACKAGES:
        try:
            nltk.data.find(path)
        except LookupError:
            try:
                nltk.download(name, quiet=True)
            except Exception:
                pass

MARGIN_CHARS = 2
INITIAL_LINES = 50
DEFAULT_FONT  = "Courier"
DEFAULT_SIZE  = 12
SIZES = [8, 9, 10, 11, 12, 14, 16, 18, 20, 24, 28, 32, 36, 48, 72]
SEP_DOT = "\u00b7"   # ·  middle dot

# Penn Treebank POS tags that indicate function-word position.
# Words in these positions are typically unstressed in running speech.
_FUNCTION_POS = frozenset({
    "CC",   # coordinating conjunction   and, or, but, nor, yet, so
    "DT",   # determiner                 the, a, an, this, that
    "EX",   # existential there
    "IN",   # preposition / sub. conj.   of, to, in, for, on, with, at, by
    "MD",   # modal auxiliary            will, would, can, could, shall, should
    "PDT",  # predeterminer
    "POS",  # possessive ending          's
    "PRP",  # personal pronoun           he, she, it, they, we, you, me
    "PRP$", # possessive pronoun         my, his, her, its, our, their
    "RP",   # particle                   up, out, off (as verb particles)
    "TO",   # infinitival to
    "WDT",  # wh-determiner              which, that
    "WP",   # wh-pronoun                 who, what
    "WP$",  # possessive wh-pronoun      whose
    "WRB",  # wh-adverb                  how, where, when, why
})

# Degree / weak adverbs that are typically unstressed in running speech.
_WEAK_WORDS = frozenset({
    'so', 'too', 'very', 'quite', 'rather', 'just',
})

# Auxiliaries (modern + archaic) — self-destress in running speech.
_AUXILIARIES = frozenset({
    'be', 'is', 'am', 'are', 'was', 'were', 'been', 'being',
    'have', 'has', 'had', 'having',
    'do', 'does', 'did',
    'will', 'would', 'shall', 'should',
    'can', 'could', 'may', 'might', 'must',
    # archaic / poetic forms
    'hath', 'doth', 'wilt', 'shalt', 'canst',
    'wouldst', 'shouldst', 'dost',
})

# Do-support auxiliaries: "do GO a-courting" — the main verb keeps its stress.
_DO_SUPPORT = frozenset({'do', 'does', 'did', 'doth', 'dost'})

# Have-type auxiliaries: "hath MADE" → following participle destressed (perfect aspect).
# Be-type auxiliaries ("was MADE", "is SEEN") leave the participle stressed (passive).
_HAVE_AUX = frozenset({'have', 'has', 'had', 'having', 'hath', 'hadst'})

_FONT_CANDIDATES = [
    "Courier", "Courier New", "Courier 10 Pitch",
    "DejaVu Sans Mono", "FreeMono", "Liberation Mono",
    "Lucida Console", "Consolas", "Menlo", "Monaco", "Ubuntu Mono", "Monospace",
    "Arial", "Helvetica", "DejaVu Sans", "FreeSans",
    "Liberation Sans", "Tahoma", "Verdana", "Ubuntu", "Noto Sans",
    "Times", "Times New Roman", "Georgia",
    "DejaVu Serif", "FreeSerif", "Liberation Serif", "Noto Serif", "Palatino",
]


def _meta_path(txt_path):
    return txt_path + ".meta"


class _MeterWorker(threading.Thread):
    """Compute meter strings for all lines in a background thread.

    Marshals UI updates back to the main thread via `root.after(0, …)`
    so the editor stays responsive while meter rows fill in.
    """
    def __init__(self, editor):
        super().__init__(daemon=True)
        self._ed = editor

    def run(self):
        ed = self._ed
        # Capture a snapshot of lines so late additions don't confuse indices.
        lines = list(ed.lines)
        for i, (te, _) in enumerate(lines):
            text = te.get()
            # _compose_meter_line touches NLTK/CMU/spaCy but not the UI.
            meter_text = ed._compose_meter_line(text) if text else ''
            # Schedule the UI update on the main thread.
            ed.root.after(0, lambda idx=i, txt=meter_text: ed._update_meter_line(idx, txt))
        ed.root.after(0, ed._meter_done)


class Editor:
    def __init__(self, root, _preloaded=None):
        self.root = root
        self.lines        = []   # [(text_entry, margin_entry), ...]
        self._line_meta   = []   # parallel list of character run-lists
        self._meter_rows  = []   # parallel list of tk.Text meter widgets
        self._rhyme_cells = []   # parallel list of rhyme-scheme indicator entries
        self._current_path = None
        self._repo_path    = None  # active git repository
        self._is_dirty     = False
        self._sel_anchor   = None
        self._sel_focus    = None
        self._click_row    = None
        self._click_index  = None

        pre = _preloaded or {}
        if "cmu" in pre:
            _ensure_nltk_data()
            self._cmu = pre["cmu"]
            self._syl_tok = pre.get("syl_tok") or SyllableTokenizer()
            self._rhyme_dict = pre.get("rhyme_dict") or self._load_rhyme_dict()
        else:
            _ensure_nltk_data()
            self._cmu = cmudict.dict()
            self._syl_tok = SyllableTokenizer()
            self._rhyme_dict = self._load_rhyme_dict()
        self._thesaurus  = None  # loaded lazily on first use
        self._thesaurus_loading = False
        self._spacy_nlp  = None  # loaded lazily on first use
        self._spacy_loading = False
        if _SPACY_AVAILABLE:
            threading.Thread(target=self._load_spacy_background, daemon=True).start()
        threading.Thread(target=self._load_thesaurus_background, daemon=True).start()

        self._last_focus_row    = None
        self._last_focus_cursor = 0

        self._font_var  = tk.StringVar(value=DEFAULT_FONT)
        self._size_var  = tk.IntVar(value=DEFAULT_SIZE)
        self._tk_font   = tkfont.Font(family=DEFAULT_FONT, size=DEFAULT_SIZE)
        self._char_w    = self._tk_font.measure("0")
        self._meter_var = tk.BooleanVar(value=False)

        sys_fonts = set(tkfont.families())
        self._avail_fonts = [f for f in _FONT_CANDIDATES if f in sys_fonts]
        if not self._avail_fonts:
            self._avail_fonts = sorted(sys_fonts)[:40]

        self._build_ui()
        self._populate(INITIAL_LINES)
        init_w = (80 + MARGIN_CHARS) * self._char_w + 20
        self.root.geometry(f"{init_w}x600")
        self._update_title()
        self.root.protocol("WM_DELETE_WINDOW", self._quit)

        # Restore last-used repository from state
        saved_repo = self._load_repo_state()
        if saved_repo and os.path.exists(saved_repo):
            try:
                Repo(saved_repo)
                self._repo_path = saved_repo
            except _dulwich_errors.NotGitRepository:
                pass  # stale state entry, ignore

    # ------------------------------------------------------------------ #
    # Font
    # ------------------------------------------------------------------ #

    def _font_spec(self):
        return (self._font_var.get(), self._size_var.get())

    def _apply_font(self):
        fname, fsize = self._font_var.get(), self._size_var.get()
        spec = (fname, fsize)
        self._tk_font = tkfont.Font(family=fname, size=fsize)
        self._char_w  = self._tk_font.measure("0")
        self.inner.columnconfigure(1, weight=0, minsize=self._char_w * MARGIN_CHARS)
        self.inner.columnconfigure(2, weight=0, minsize=self._char_w)
        for i, (te, me) in enumerate(self.lines):
            te.configure(font=spec)
            me.configure(font=spec)
            if i < len(self._rhyme_cells):
                self._rhyme_cells[i].configure(font=spec)
            text = te.get()
            self._line_meta[i] = (
                [{"font": fname, "size": fsize, "len": len(text)}] if text else []
            )
        if self._meter_var.get():
            self._show_meter()

    # ------------------------------------------------------------------ #
    # Character-level runs
    # ------------------------------------------------------------------ #

    def _runs_for_line(self, i):
        text     = self.lines[i][0].get()
        text_len = len(text)
        runs     = list(self._line_meta[i])
        fname, fsize = self._font_var.get(), self._size_var.get()
        run_total = sum(r["len"] for r in runs)

        if run_total < text_len:
            extra = text_len - run_total
            if runs and runs[-1]["font"] == fname and runs[-1]["size"] == fsize:
                runs[-1] = {**runs[-1], "len": runs[-1]["len"] + extra}
            else:
                runs.append({"font": fname, "size": fsize, "len": extra})
        elif run_total > text_len:
            result, remaining = [], text_len
            for r in runs:
                if remaining <= 0:
                    break
                take = min(r["len"], remaining)
                result.append({**r, "len": take})
                remaining -= take
            runs = result
        return runs

    # ------------------------------------------------------------------ #
    # Syllable counting (margin field)
    # ------------------------------------------------------------------ #

    def _best_cmu_entry(self, word):
        """Return the best cmudict entry for syllable counting.

        When all entries agree (the common case) entries[0] is returned
        unchanged.  When they disagree, return the entry with the fewest
        syllables: in verse the contracted/syncopated pronunciation is almost
        always the intended one (e.g. "every" → ev-ry 2, "ourselves" → 2,
        "different" → diff-rent 2).  Ties favour entries[0].

        Returns None if the word is not in cmudict."""
        entries = self._cmu.get(word.lower())
        if not entries:
            return None
        if len(entries) == 1:
            return entries[0]
        counts = [sum(1 for ph in e if ph[-1].isdigit()) for e in entries]
        if len(set(counts)) == 1:          # all pronunciations agree
            return entries[0]
        # Prefer the fewest-syllable pronunciation; tie-break by index.
        best_idx = min(range(len(counts)), key=lambda i: (counts[i], i))
        return entries[best_idx]

    def _cmu_syllables(self, word):
        entry = self._best_cmu_entry(word)
        if entry is not None:
            return sum(1 for ph in entry if ph[-1].isdigit())
        return None

    def _fallback_syllables(self, word):
        if not word:
            return 0
        return max(1, len(self._syl_tok.tokenize(word.lower())))

    # ------------------------------------------------------------------ #
    # Rhyme dictionary
    # ------------------------------------------------------------------ #

    @staticmethod
    def _load_rhyme_dict_static():
        """Load rhyme dict outside of Editor (used by splash screen)."""
        content = _read_data('rdict.js')
        if not content:
            return {}
        start = content.index('var rhdict = ') + len('var rhdict = ')
        end   = content.index('\nvar spdict = ')
        return json.loads(content[start:end].rstrip(';\n '))

    def _load_rhyme_dict(self):
        return self._load_rhyme_dict_static()

    # ------------------------------------------------------------------ #
    # Thesaurus
    # ------------------------------------------------------------------ #

    def _load_thesaurus_background(self):
        """Pre-load thesaurus data in a background thread."""
        if self._thesaurus is not None or self._thesaurus_loading:
            return
        self._thesaurus_loading = True
        try:
            self._thesaurus = self._load_thesaurus()
        except Exception:
            self._thesaurus = {}
        finally:
            self._thesaurus_loading = False

    def _load_thesaurus(self):
        """Parse th_en_US_new.js lazily; returns dict {word: [synonym, ...]}."""
        raw = _read_data('th_en_US_new.js')
        if not raw:
            return {}
        raw = raw.strip()
        if raw.startswith('module.exports = '):
            raw = raw[len('module.exports = '):]
        if raw.endswith(';'):
            raw = raw[:-1]
        return json.loads(raw)

    def _get_thesaurus(self, word):
        """Return sorted list of synonyms for word (excluding the word itself)."""
        if self._thesaurus is None and not self._thesaurus_loading:
            self._thesaurus = self._load_thesaurus()
        key = word.lower()
        syns = (self._thesaurus or {}).get(key, [])
        # Filter out the headword itself; deduplicate while preserving order
        seen, result = {key}, []
        for s in syns:
            sl = s.lower()
            if sl not in seen:
                seen.add(sl)
                result.append(s)
        return result

    def _thesaurus_click(self):
        if self._last_focus_row is not None:
            row  = self._last_focus_row
            te   = self.lines[row][0]
            text = te.get()
            try:
                cursor = te.index(tk.INSERT)
            except tk.TclError:
                cursor = self._last_focus_cursor
            word, ws, we = self._word_at_cursor(text, cursor)
            if word:
                self._show_thesaurus_popup(word, self._get_thesaurus(word), row, ws, we)
                return
            messagebox.showinfo("Thesaurus", "Place the cursor on or after a word.")
            return
        messagebox.showinfo("Thesaurus", "Click in your poem first, then press Thesaurus.")

    def _about_click(self):
        popup = tk.Toplevel(self.root)
        popup.title("About Poedit")
        popup.transient(self.root)
        popup.resizable(False, False)

        # Read about.txt
        about_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), "about.txt")
        about_text = ""
        if os.path.exists(about_path):
            with open(about_path, "r", encoding="utf-8") as f:
                about_text = f.read()

        # Text pane
        text_frame = tk.Frame(popup, bg="white")
        text_frame.pack(fill="both", expand=True, padx=12, pady=8)

        text_widget = tk.Text(
            text_frame, wrap="word", font=("TkDefaultFont", 10),
            bg="white", relief="flat", padx=6, pady=6,
            width=50, height=12,
        )
        text_widget.insert("1.0", about_text)
        text_widget.config(state="disabled")

        scrollbar = tk.Scrollbar(text_frame, orient="vertical", command=text_widget.yview)
        text_widget.config(yscrollcommand=scrollbar.set)

        scrollbar.pack(side="right", fill="y")
        text_widget.pack(side="left", fill="both", expand=True)

        # QR code image
        qr_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), "qr-code.png")
        if os.path.exists(qr_path):
            try:
                from PIL import Image as _PILImage, ImageTk as _PILImageTk
                img = _PILImage.open(qr_path).resize((150, 150), _PILImage.LANCZOS)
                photo = _PILImageTk.PhotoImage(img)
                qr_label = tk.Label(popup, image=photo)
                qr_label.image = photo  # keep a reference
                qr_label.pack(pady=(0, 8))

                tk.Label(
                    popup, text="Scan for support & project info",
                    font=("TkDefaultFont", 9), fg="gray",
                ).pack(pady=(0, 8))
            except Exception:
                pass

        tk.Button(popup, text="Close", command=popup.destroy).pack(pady=(0, 10))

    # ------------------------------------------------------------------ #
    # Version Control (Dulwich / Git)
    # ------------------------------------------------------------------ #

    def _load_repo_state(self):
        """Load last-used repository path from state file."""
        if not os.path.exists(_STATE_FILE):
            return None
        try:
            with open(_STATE_FILE, "r", encoding="utf-8") as f:
                state = json.load(f)
            return state.get("last_repo")
        except Exception:
            return None

    def _save_repo_state(self, repo_path):
        """Save current repository path to state file."""
        os.makedirs(_STATE_DIR, exist_ok=True)
        state = {}
        if os.path.exists(_STATE_FILE):
            try:
                with open(_STATE_FILE, "r", encoding="utf-8") as f:
                    state = json.load(f)
            except Exception:
                pass
        state["last_repo"] = repo_path
        with open(_STATE_FILE, "w", encoding="utf-8") as f:
            json.dump(state, f, indent=2)

    def _new_repo(self):
        """Create a new git repository and set up the poems directory."""
        popup = tk.Toplevel(self.root)
        popup.title("New Repository")
        popup.transient(self.root)
        popup.resizable(False, False)
        popup.grab_set()

        tk.Label(popup, text="Repository name:").pack(anchor="w", padx=12, pady=(10, 2))
        name_var = tk.StringVar(value="poetry")
        name_entry = tk.Entry(popup, textvariable=name_var, width=40)
        name_entry.pack(anchor="w", padx=12)
        name_entry.focus_set()
        name_entry.select_range(0, tk.END)

        tk.Label(popup, text="Location:").pack(anchor="w", padx=12, pady=(8, 2))
        path_var = tk.StringVar(value=os.path.join(os.path.expanduser("~"), "Documents"))
        path_frame = tk.Frame(popup)
        path_frame.pack(anchor="w", padx=12)
        path_entry = tk.Entry(path_frame, textvariable=path_var, width=32)
        path_entry.pack(side="left")
        tk.Button(
            path_frame, text="Browse\u2026",
            command=lambda: _browse(),
        ).pack(side="left", padx=(4, 0))

        def _browse():
            d = filedialog.askdirectory(
                title="Select Parent Directory",
                initialdir=path_var.get() or os.path.expanduser("~"),
            )
            if d:
                path_var.set(d)

        def _do_create():
            name = name_var.get().strip()
            base = path_var.get().strip()
            if not name:
                messagebox.showwarning("Error", "Repository name is required.")
                return
            if not base:
                messagebox.showwarning("Error", "Location is required.")
                return
            repo_dir = os.path.join(base, name)
            if os.path.exists(repo_dir):
                # If it's already a valid git repo, reuse it
                try:
                    Repo(repo_dir).close()
                    self._repo_path = repo_dir
                    self._save_repo_state(repo_dir)
                    self._current_path = None
                    self._new()
                    self._update_title()
                    popup.destroy()
                    return
                except _dulwich_errors.NotGitRepository:
                    messagebox.showerror("Error", f"Directory already exists and is not a Git repo:\n{repo_dir}")
                    return
            os.makedirs(repo_dir)
            try:
                Repo.init(repo_dir)
                self._repo_path = repo_dir
                self._save_repo_state(repo_dir)

                if self._current_path or self._is_dirty:
                    # Save current poem into the repository, even if it was from
                    # outside the repo — copy it in.
                    src_name = os.path.basename(self._current_path) if self._current_path else "poem.txt"
                    dest = os.path.join(repo_dir, src_name)
                    self._write_files(dest)
                    self._do_commit_and_stage("Initial commit")
                else:
                    self._new()
                self._update_title()
                popup.destroy()
            except Exception as exc:
                messagebox.showerror("Error", f"Could not create repository:\n{exc}")

        tk.Button(popup, text="Create Repository", command=_do_create).pack(pady=12)
        name_entry.bind("<Return>", lambda e: _do_create())

    def _open_repo(self):
        """Open an existing repository and show its contents."""
        if not self._confirm_discard():
            return
        last_repo = self._load_repo_state()
        repo_path = filedialog.askdirectory(
            title="Select Repository",
            initialdir=last_repo or os.path.expanduser("~"),
        )
        if not repo_path:
            return
        try:
            repo = Repo(repo_path)
            repo.close()
        except _dulwich_errors.NotGitRepository:
            messagebox.showerror("Error", "Not a valid Git repository.")
            return
        self._repo_path = repo_path
        self._save_repo_state(repo_path)
        self._show_repo_browser(repo_path)

    def _show_repo_browser(self, repo_path):
        """Show a dialog listing the repository's .txt files."""
        popup = tk.Toplevel(self.root)
        popup.title(f"Repository: {os.path.basename(repo_path)}")
        popup.transient(self.root)
        popup.geometry("500x400")

        repo = Repo(repo_path)
        try:
            head = repo.head()
            tree = repo[repo[head].tree]
        except Exception:
            head = None
            tree = None

        files = []
        if tree is not None:
            for entry in tree.items():
                if entry.path.endswith(b".txt") and not entry.path.endswith(b".meta"):
                    obj = repo[entry.sha]
                    if isinstance(obj, Blob):
                        files.append({
                            "name": os.path.basename(entry.path.decode()),
                            "path": entry.path.decode(),
                            "sha": entry.sha.hex(),
                            "mtime": 0,
                        })

        # Sort control
        sort_mode = tk.StringVar(value="alpha")
        toolbar = tk.Frame(popup)
        toolbar.pack(fill="x", padx=6, pady=4)
        tk.Label(toolbar, text="Sort:").pack(side="left", padx=(0, 4))
        tk.Radiobutton(
            toolbar, text="Alphabetical", variable=sort_mode, value="alpha",
            command=lambda: _refresh(),
        ).pack(side="left", padx=4)
        tk.Radiobutton(
            toolbar, text="Chronological", variable=sort_mode, value="chrono",
            command=lambda: _refresh(),
        ).pack(side="left", padx=4)

        def _refresh():
            for w in listbox.winfo_children():
                w.destroy()
            mode = sort_mode.get()
            sorted_files = sorted(files, key=lambda f: f["name"] if mode == "alpha" else f["mtime"])
            for fi in sorted_files:
                item_frame = tk.Frame(listbox, bg="white")
                item_frame.pack(fill="x", padx=2, pady=1)
                btn = tk.Button(
                    item_frame, text=fi["name"], relief="flat", bg="white",
                    anchor="w",
                    command=lambda p=fi["path"]: _open_file_from_repo(repo_path, p),
                )
                btn.pack(fill="x", expand=True)

        listbox = tk.Frame(popup, bg="white")
        listbox.pack(fill="both", expand=True, padx=6, pady=4)

        cv = tk.Canvas(listbox, bg="white")
        sb = tk.Scrollbar(listbox, orient="vertical", command=cv.yview)
        cv.configure(yscrollcommand=sb.set)
        inner = tk.Frame(cv, bg="white")
        cv.create_window((0, 0), window=inner, anchor="nw")
        inner.bind("<Configure>", lambda e: cv.configure(scrollregion=cv.bbox("all")))
        cv.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")

        listbox.cv = cv
        listbox.inner = inner

        _refresh()

        def _open_file_from_repo(rpath, rel_path):
            full_path = os.path.join(rpath, rel_path)
            if not self._confirm_discard():
                popup.destroy()
                return
            self._repo_path = rpath
            self._load_file(full_path)
            popup.destroy()

    def _version_click(self):
        """Create a named version (commit) of the current poem."""
        if not getattr(self, "_repo_path", None):
            messagebox.showinfo("Version", "No repository is open. Use File > New Repository or Open Repository first.")
            return
        if not self._current_path:
            # Ask for a filename inside the repo — simple text entry, no file selection
            popup_save = tk.Toplevel(self.root)
            popup_save.title("Save Poem in Repository")
            popup_save.transient(self.root)
            popup_save.resizable(False, False)
            popup_save.grab_set()

            tk.Label(popup_save, text="File name:").pack(anchor="w", padx=12, pady=(10, 2))
            name_var = tk.StringVar()
            name_entry = tk.Entry(popup_save, textvariable=name_var, width=40)
            name_entry.pack(anchor="w", padx=12)
            name_entry.focus_set()
            name_entry.insert(0, "poem.txt")
            name_entry.select_range(0, tk.END)

            result_path = {"value": None}

            def _do_save():
                fname = name_var.get().strip()
                if not fname:
                    messagebox.showwarning("Error", "File name is required.")
                    return
                if not fname.endswith(".txt"):
                    fname += ".txt"
                dest = os.path.join(self._repo_path, fname)
                if os.path.exists(dest):
                    if not messagebox.askyesno("Overwrite", f"{fname} already exists. Overwrite?"):
                        return
                result_path["value"] = dest
                popup_save.destroy()

            tk.Button(popup_save, text="Save", command=_do_save).pack(pady=12)
            name_entry.bind("<Return>", lambda e: _do_save())
            popup_save.wait_window()

            name = result_path["value"]
            if not name:
                return
            # Ensure the path is inside the repo
            rel = os.path.relpath(name, self._repo_path)
            if rel.startswith(".."):
                messagebox.showerror("Error", "File must be inside the repository directory.")
                return
            self._current_path = name
            self._write_files(name)

        now_str = self._timestamp_now()
        message = tk.StringVar(value=now_str)

        popup = tk.Toplevel(self.root)
        popup.title("Create Version")
        popup.transient(self.root)
        popup.resizable(False, False)

        tk.Label(popup, text="Version message:").pack(anchor="w", padx=12, pady=(8, 2))
        entry = tk.Entry(popup, textvariable=message, width=50)
        entry.pack(anchor="w", padx=12)
        entry.focus_set()
        entry.select_range(0, tk.END)

        def _do_commit():
            msg = message.get().strip()
            if not msg:
                msg = now_str
            self._do_commit_and_stage(msg)
            popup.destroy()

        tk.Button(popup, text="Commit", command=_do_commit).pack(pady=10)
        entry.bind("<Return>", lambda e: _do_commit())

    def _timestamp_now(self):
        from datetime import datetime
        return datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    def _do_commit_and_stage(self, message):
        """Save current editor to disk, then stage and commit if changed."""
        if not getattr(self, "_repo_path", None) or not self._current_path:
            return False
        try:
            # Write current editor content to disk before committing
            self._write_files(self._current_path)

            rel = os.path.relpath(self._current_path, self._repo_path)
            meta_path = _meta_path(self._current_path)
            meta_rel = os.path.relpath(meta_path, self._repo_path) if os.path.exists(meta_path) else None

            _porcelain.add(self._repo_path, paths=[rel])
            if meta_rel:
                _porcelain.add(self._repo_path, paths=[meta_rel])

            # Check if there are any staged or unstaged changes before committing
            repo = Repo(self._repo_path)
            try:
                st = _porcelain.status(self._repo_path)
                s = st.staged  # {'add': [], 'delete': [], 'modify': []}
                has_changes = bool(s.get('add') or s.get('delete') or s.get('modify') or st.unstaged)
            except Exception:
                has_changes = True  # if status check fails, assume changed
            repo.close()

            if not has_changes:
                return False  # nothing to commit

            _porcelain.commit(
                self._repo_path,
                message=message.encode("utf-8"),
                author=b"Poetit User <poetit@local>",
            )
            return True
        except Exception as exc:
            messagebox.showerror("Commit Error", f"Could not create version:\n{exc}")
            return False

    def _save_recovery(self):
        """Save current unsaved edits to a recovery file in the repo."""
        repo = getattr(self, "_repo_path", None)
        if not repo:
            return None
        recovery_dir = os.path.join(repo, ".poetit-recovery")
        os.makedirs(recovery_dir, exist_ok=True)
        from datetime import datetime
        ts = datetime.now().strftime("%Y%m%d-%H%M%S")
        recovery_name = f"unsaved-{ts}.txt"
        recovery_path = os.path.join(recovery_dir, recovery_name)
        content = [te.get() for te, _ in self.lines]
        while content and not content[-1]:
            content.pop()
        if not content:
            return None
        with open(recovery_path, "w", encoding="utf-8") as f:
            f.write("\n".join(content) + "\n")
        self._mark_clean()
        return recovery_path

    def _load_blob_at_path(self, commit_sha, rel_path):
        """Extract the content of a blob from a specific commit."""
        if isinstance(commit_sha, str):
            commit_sha = commit_sha.encode()
        repo = Repo(self._repo_path)
        try:
            commit = repo[commit_sha]
            tree = repo[commit.tree]
            # Walk the tree to find the file
            parts = rel_path.split("/")
            current = tree
            for part in parts[:-1]:
                entry = None
                for e in current.items():
                    if e.path.decode() == part:
                        entry = repo[e.sha]
                        break
                if entry is None:
                    return None
                current = entry
            # Find the file
            filename = parts[-1]
            for e in current.items():
                if e.path.decode() == filename:
                    blob = repo[e.sha]
                    return blob.data
            return None
        except Exception:
            return None
        finally:
            repo.close()

    def _load_text_into_editor(self, text):
        """Replace editor content with given text."""
        file_lines = text.splitlines()
        while len(self.lines) < max(len(file_lines), INITIAL_LINES):
            self._add_row()
        self._trim_rows(max(len(file_lines), INITIAL_LINES))
        for i, (te, me) in enumerate(self.lines):
            te.delete(0, tk.END)
            self._line_meta[i] = []
            me.configure(state="normal")
            me.delete(0, tk.END)
            me.configure(state="readonly")
        for i, line in enumerate(file_lines):
            self.lines[i][0].insert(0, line)
        fname, fsize = self._font_var.get(), self._size_var.get()
        for i, line in enumerate(file_lines):
            self._line_meta[i] = (
                [{"font": fname, "size": fsize, "len": len(line)}] if line else []
            )
        for i in range(len(file_lines)):
            self._update_margin(i)
        self._update_rhyme_scheme()
        if self._meter_var.get():
            self._show_meter()

    def _tree_click(self):
        """Show a graphical version tree dialog."""
        if not getattr(self, "_repo_path", None):
            messagebox.showinfo("Version Tree", "No repository is open.")
            return
        self._show_version_tree()

    def _show_version_tree(self):
        """Display a scrollable tree of commits with selectable/loadable versions."""
        popup = tk.Toplevel(self.root)
        popup.title("Version Tree")
        popup.transient(self.root)
        popup.geometry("650x500")

        from datetime import datetime
        repo = Repo(self._repo_path)

        # Collect all commits with their trees
        commits = []
        try:
            head_sha = repo.head()
        except KeyError:
            head_sha = None

        if head_sha:
            try:
                walker = repo.get_walker(head_sha)
                for entry in walker:
                    c = entry.commit
                    # Collect file paths from the tree
                    tree = repo[c.tree]
                    files = []
                    for e in tree.items():
                        if e.path.endswith(b".txt") and not e.path.endswith(b".meta"):
                            files.append(e.path.decode())
                    commits.append({
                        "sha": c.id.decode()[:8],
                        "sha_full": c.id,
                        "message": c.message.decode("utf-8", errors="replace").strip(),
                        "author": c.author.decode("utf-8", errors="replace"),
                        "time": datetime.fromtimestamp(c.commit_time).strftime("%Y-%m-%d %H:%M"),
                        "parents": [p.decode()[:8] for p in c.parents],
                        "files": files,
                    })
            except Exception as exc:
                messagebox.showerror("Error", f"Could not read commits:\n{exc}")
                repo.close()
                return
        repo.close()

        # Status bar at the bottom
        status_var = tk.StringVar(value="Click a version to load it into the editor.")

        # Build a canvas-based tree view
        cv = tk.Canvas(popup, bg="white")
        v_sb = tk.Scrollbar(popup, orient="vertical", command=cv.yview)
        cv.configure(yscrollcommand=v_sb.set)
        cv.pack(side="left", fill="both", expand=True)
        v_sb.pack(side="right", fill="y")

        tk.Label(popup, textvariable=status_var, anchor="w", relief="sunken", bd=1).pack(fill="x", padx=2, pady=2)

        inner = tk.Frame(cv, bg="white")
        cv.create_window((0, 0), window=inner, anchor="nw")
        inner.bind("<Configure>", lambda e: cv.configure(scrollregion=cv.bbox("all")))

        # Build the tree layout
        sha_to_idx = {c["sha"]: i for i, c in enumerate(commits)}
        y_step = 60
        x_base = 40
        col_step = 80

        # Determine the "active file" for this tree session — the file the user
        # was editing when they opened the tree.
        active_file = None
        if getattr(self, "_current_path", None):
            active_rel = os.path.relpath(self._current_path, self._repo_path)
            for c in commits:
                if active_rel in c["files"]:
                    active_file = active_rel
                    break
        if active_file is None and commits:
            if commits[0]["files"]:
                active_file = commits[0]["files"][0]

        # Filter commits to only those containing the active file
        if active_file:
            commits = [c for c in commits if active_file in c["files"]]

        # Show file indicator in status
        if active_file:
            status_var.set(f"Showing: {active_file}  —  click a version to load it.")
        else:
            status_var.set("No poem files found in this repository.")

        def _load_version(c):
            """Load a specific version into the editor."""
            if not active_file:
                status_var.set("No active file to load.")
                return

            if active_file not in c["files"]:
                status_var.set(f"{active_file} not in this version.")
                return

            data = self._load_blob_at_path(c["sha_full"], active_file)
            if data is None:
                status_var.set(f"Could not load {active_file} from {c['sha']}")
                return
            text = data.decode("utf-8", errors="replace")
            self._load_text_into_editor(text)
            self._current_path = os.path.join(self._repo_path, active_file)
            self._mark_clean()
            self._update_title()
            status_var.set(f"Loaded: {active_file} @ {c['sha']}  |  {c['message']}")

        # Simple linear layout with parent lines
        for i, c in enumerate(commits):
            y = i * y_step + 20
            # Determine column based on parent branching
            col = 0
            if c["parents"]:
                parent_idx = sha_to_idx.get(c["parents"][0])
                if parent_idx is not None:
                    col = len(c["parents"]) - 1

            x = x_base + col * col_step

            # Draw connector line to parent
            if c["parents"]:
                parent_idx = sha_to_idx.get(c["parents"][0])
                if parent_idx is not None:
                    py = parent_idx * y_step + 20
                    cv.create_line(x, py + 20, x, y - 10, fill="#888", width=2)

            # Commit node — clickable
            node = tk.Frame(inner, bg="#e8f0ff", bd=1, relief="solid", cursor="hand2")
            node.place(x=x, y=y, width=380, height=40)

            lbl1 = tk.Label(
                node, text=f'{c["sha"]}  {c["time"]}',
                font=("TkDefaultFont", 8), bg="#e8f0ff", anchor="w",
            )
            lbl1.pack(fill="x", padx=4, pady=(2, 0))
            lbl2 = tk.Label(
                node, text=c["message"][:60],
                font=("TkDefaultFont", 9, "bold"), bg="#e8f0ff", anchor="w",
            )
            lbl2.pack(fill="x", padx=4)

            # Bind click on node and all its children
            for w in (node, lbl1, lbl2):
                w.bind("<Button-1>", lambda e, cc=c: _load_version(cc))

            # Fork button
            btn_frame = tk.Frame(inner, bg="white")
            btn_frame.place(x=x + 390, y=y + 10)

            tk.Button(
                btn_frame, text="Fork", font=("TkDefaultFont", 8),
                command=lambda sha=c["sha_full"], msg=c["message"]: _fork_to_head(sha, msg, popup),
            ).pack(side="top")

        # Set inner frame size
        total_h = max(len(commits) * y_step + 80, 400)
        inner.configure(width=560, height=total_h)

        def _fork_to_head(sha, msg, win):
            """Create a new branch from the selected commit and set HEAD to it."""
            sha_short = sha[:8] if isinstance(sha, (str, bytes)) else sha.decode()[:8]
            from datetime import datetime
            branch_name = f"fork-{datetime.now().strftime('%Y%m%d-%H%M%S')}"
            if msg:
                branch_name += f"-{msg[:20].replace(' ', '-')}"
            if not messagebox.askyesno(
                "Fork Branch",
                f"Create branch '{branch_name}' at {sha_short} and check it out?",
            ):
                return
            try:
                repo = Repo(self._repo_path)
                # Create branch ref
                ref_name = f"refs/heads/{branch_name}"
                repo.refs[ref_name.encode()] = sha
                # Point HEAD to the new branch
                repo.refs[b"HEAD"] = ref_name.encode()
                repo.close()
                messagebox.showinfo("Fork", f"Created and checked out:\n{branch_name}")
                win.destroy()
                self._show_version_tree()  # refresh
            except Exception as exc:
                messagebox.showerror("Error", str(exc))

    def _show_thesaurus_popup(self, word, synonyms, row, ws, we):
        popup = tk.Toplevel(self.root)
        popup.title(f'Thesaurus: "{word}"')
        popup.transient(self.root)
        popup.resizable(False, True)

        if row is not None:
            header_txt = f'Click to replace in line {row + 1}:'
        else:
            header_txt = 'Synonyms:'
        tk.Label(popup, text=header_txt, anchor='w').pack(fill=tk.X, padx=6, pady=(6, 2))

        if not synonyms:
            tk.Label(popup, text='No synonyms found.', fg='gray').pack(padx=6, pady=6)
            tk.Button(popup, text='Close', command=popup.destroy).pack(pady=6)
            return

        outer = tk.Frame(popup)
        outer.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)

        cv = tk.Canvas(outer, width=240, height=380, bg='white')
        sb = tk.Scrollbar(outer, orient='vertical', command=cv.yview)
        cv.configure(yscrollcommand=sb.set)
        cv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.pack(side=tk.RIGHT, fill=tk.Y)

        inner = tk.Frame(cv, bg='white')
        cv.create_window((0, 0), window=inner, anchor='nw')

        for syn in synonyms:
            if row is not None:
                def cmd(s=syn):
                    self._insert_synonym(s, row, ws, we)
                    popup.destroy()
            else:
                cmd = popup.destroy
            tk.Button(
                inner, text=syn, anchor='w', relief='flat',
                bg='white', activebackground='#ddeeff', command=cmd,
            ).pack(fill=tk.X, padx=2, pady=1)

        inner.update_idletasks()
        cv.configure(scrollregion=cv.bbox('all'))

        def _scroll(event):
            if event.num == 4:   cv.yview_scroll(-1, 'units')
            elif event.num == 5: cv.yview_scroll(1, 'units')
            else:                cv.yview_scroll(int(-1 * (event.delta / 120)), 'units')
        for seq in ('<MouseWheel>', '<Button-4>', '<Button-5>'):
            cv.bind(seq, _scroll)
            inner.bind(seq, _scroll)

    def _insert_synonym(self, synonym, row, ws, we):
        te       = self.lines[row][0]
        text     = te.get()
        new_text = text[:ws] + synonym + text[we:]
        te.delete(0, tk.END)
        te.insert(0, new_text)
        te.icursor(ws + len(synonym))
        self._update_margin(row)
        if self._meter_var.get() and row < len(self._meter_rows):
            self._fill_meter_widget(self._meter_rows[row], new_text)

    def _get_rhymes(self, word):
        """Return list of words that rhyme with word, using rdict.js algorithm."""
        if not self._rhyme_dict:
            return []
        entries = self._cmu.get(word.lower())
        if not entries:
            return []
        # Strip stress digits and reverse phoneme list
        phonemes = [re.sub(r'\d', '', ph) for ph in entries[0]]
        rev = list(reversed(phonemes))
        key = rev[0]
        if key not in self._rhyme_dict:
            return []
        results = []
        for s in range(len(rev) - 1, 0, -1):
            st   = ' '.join(rev[:s + 1])
            stl  = len(st)
            for entry in self._rhyme_dict[key]:
                if entry[:stl] == st:
                    results.append(entry.split()[-1])
        seen, unique = set(), []
        for w in results:
            if w not in seen and w.lower() != word.lower():
                seen.add(w)
                unique.append(w)
        return unique

    def _word_at_cursor(self, text, idx):
        """Return (word, start, end) of the alphabetic word touching idx."""
        idx = max(0, min(idx, len(text)))   # clamp: guard against stale cursor
        # Expand left then right from idx
        start = idx
        while start > 0 and text[start - 1].isalpha():
            start -= 1
        end = idx
        while end < len(text) and text[end].isalpha():
            end += 1
        if start < end:
            return text[start:end], start, end
        # Cursor is between words; scan left for nearest word
        end = idx
        while end > 0 and not text[end - 1].isalpha():
            end -= 1
        start = end
        while start > 0 and text[start - 1].isalpha():
            start -= 1
        return text[start:end], start, end

    # ------------------------------------------------------------------ #
    # Rhyme UI
    # ------------------------------------------------------------------ #

    def _on_focus_in(self, row):
        self._last_focus_row = row

    def _on_focus_out(self, row):
        if row < len(self.lines):
            try:
                self._last_focus_cursor = self.lines[row][0].index(tk.INSERT)
            except tk.TclError:
                self._last_focus_cursor = 0

    def _rhyme_click(self):
        if self._last_focus_row is not None:
            row  = self._last_focus_row
            te   = self.lines[row][0]
            text = te.get()
            # Read the insertion mark directly; tkinter preserves it after focus loss.
            # Fall back to the value saved by FocusOut only if that fails.
            try:
                cursor = te.index(tk.INSERT)
            except tk.TclError:
                cursor = self._last_focus_cursor
            word, ws, we = self._word_at_cursor(text, cursor)
            if word:
                self._show_rhyme_popup(word, self._get_rhymes(word), row, ws, we)
            else:
                messagebox.showinfo("Rhyme", "Place the cursor on or after a word.")
            return
        # No poem focus — reveal lookup field and inform
        self._rhyme_input.pack(side="left", padx=(0, 6), pady=3)
        messagebox.showinfo(
            "Rhyme",
            "Click in your poem first to look up and insert a rhyme.\n\n"
            "Or type a word in the field next to Rhyme and press Enter."
        )

    def _rhyme_lookup_from_field(self, _event=None):
        word = self._rhyme_input_var.get().strip()
        if word:
            self._show_rhyme_popup(word, self._get_rhymes(word), None, 0, 0)

    def _show_rhyme_popup(self, word, rhymes, row, ws, we):
        popup = tk.Toplevel(self.root)
        popup.title(f'Rhymes for "{word}"')
        popup.transient(self.root)
        popup.resizable(False, True)

        if row is not None:
            header_txt = f'Click to insert into line {row + 1}:'
        else:
            header_txt = 'Rhymes (display only — click in poem to insert):'
        tk.Label(popup, text=header_txt, anchor='w').pack(
            fill=tk.X, padx=6, pady=(6, 2))

        if not rhymes:
            tk.Label(popup, text='No rhymes found.', fg='gray').pack(padx=6, pady=6)
            tk.Button(popup, text='Close', command=popup.destroy).pack(pady=6)
            return

        outer = tk.Frame(popup)
        outer.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)

        cv = tk.Canvas(outer, width=220, height=320, bg='white')
        sb = tk.Scrollbar(outer, orient='vertical', command=cv.yview)
        cv.configure(yscrollcommand=sb.set)
        cv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.pack(side=tk.RIGHT, fill=tk.Y)

        inner = tk.Frame(cv, bg='white')
        cv.create_window((0, 0), window=inner, anchor='nw')

        for rhyme in rhymes:
            if row is not None:
                def cmd(r=rhyme):
                    self._insert_rhyme(r, row, ws, we)
                    popup.destroy()
            else:
                cmd = popup.destroy
            tk.Button(
                inner, text=rhyme, anchor='w', relief='flat',
                bg='white', activebackground='#ddeeff', command=cmd,
            ).pack(fill=tk.X, padx=2, pady=1)

        inner.update_idletasks()
        cv.configure(scrollregion=cv.bbox('all'))

        def _scroll(event):
            if event.num == 4:   cv.yview_scroll(-1, 'units')
            elif event.num == 5: cv.yview_scroll(1, 'units')
            else:                cv.yview_scroll(int(-1 * (event.delta / 120)), 'units')
        for seq in ('<MouseWheel>', '<Button-4>', '<Button-5>'):
            cv.bind(seq, _scroll)
            inner.bind(seq, _scroll)

    def _insert_rhyme(self, rhyme, row, ws, we):
        te       = self.lines[row][0]
        text     = te.get()
        new_text = text[:ws] + rhyme + text[we:]
        te.delete(0, tk.END)
        te.insert(0, new_text)
        te.icursor(ws + len(rhyme))
        self._update_margin(row)
        if self._meter_var.get() and row < len(self._meter_rows):
            self._fill_meter_widget(self._meter_rows[row], new_text)

    # ------------------------------------------------------------------ #
    # Definition (WordNet)
    # ------------------------------------------------------------------ #

    _POS_LABEL = {'n': 'Noun', 'v': 'Verb', 'a': 'Adjective',
                  's': 'Adjective', 'r': 'Adverb'}

    def _definition_click(self):
        if self._last_focus_row is not None:
            row  = self._last_focus_row
            te   = self.lines[row][0]
            text = te.get()
            try:
                cursor = te.index(tk.INSERT)
            except tk.TclError:
                cursor = self._last_focus_cursor
            word, _, _ = self._word_at_cursor(text, cursor)
            if word:
                self._show_definition_popup(word)
                return
            messagebox.showinfo("Definition", "Place the cursor on or after a word.")
            return
        messagebox.showinfo(
            "Definition",
            "Click in your poem first, then press Definition."
        )

    def _show_definition_popup(self, word):
        synsets = wn.synsets(word)
        popup = tk.Toplevel(self.root)
        popup.title(f'Definition: "{word}"')
        popup.transient(self.root)
        popup.resizable(True, True)

        # ---- scrollable canvas ----
        outer = tk.Frame(popup)
        outer.pack(fill=tk.BOTH, expand=True)

        cv = tk.Canvas(outer, width=380, height=440, bg='white',
                       highlightthickness=0)
        sb = tk.Scrollbar(outer, orient='vertical', command=cv.yview)
        cv.configure(yscrollcommand=sb.set)
        cv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.pack(side=tk.RIGHT, fill=tk.Y)

        inner = tk.Frame(cv, bg='white', padx=10, pady=6)
        cv_win = cv.create_window((0, 0), window=inner, anchor='nw')

        # Expand inner frame to canvas width when window resizes
        def _on_cv_resize(event):
            cv.itemconfig(cv_win, width=event.width)
        cv.bind('<Configure>', _on_cv_resize)

        def _scroll(event):
            if event.num == 4:   cv.yview_scroll(-1, 'units')
            elif event.num == 5: cv.yview_scroll(1, 'units')
            else:                cv.yview_scroll(int(-1*(event.delta/120)), 'units')
        for seq in ('<MouseWheel>', '<Button-4>', '<Button-5>'):
            cv.bind(seq, _scroll)
            inner.bind(seq, _scroll)

        # ---- fonts ----
        f_word    = tkfont.Font(family='Helvetica', size=13, weight='bold')
        f_pos     = tkfont.Font(family='Helvetica', size=10, weight='bold',
                                slant='italic')
        f_sense   = tkfont.Font(family='Helvetica', size=10, weight='bold')
        f_def     = tkfont.Font(family='Helvetica', size=10)
        f_sub     = tkfont.Font(family='Helvetica', size=9)

        # ---- heading ----
        tk.Label(inner, text=word.lower(), font=f_word, bg='white',
                 anchor='w').pack(fill=tk.X, pady=(0, 6))

        if not synsets:
            tk.Label(inner, text='No definitions found.', font=f_def,
                     fg='gray', bg='white', anchor='w').pack(fill=tk.X)
        else:
            # Group by POS
            by_pos = {}
            for s in synsets:
                by_pos.setdefault(s.pos(), []).append(s)

            pos_order = [p for p in ('n', 'v', 'a', 's', 'r') if p in by_pos]
            for pos in pos_order:
                label = self._POS_LABEL.get(pos, pos)
                tk.Label(inner, text=label, font=f_pos, fg='#555',
                         bg='white', anchor='w').pack(fill=tk.X, pady=(8, 2))

                for idx, s in enumerate(by_pos[pos], 1):
                    # Sense number + definition
                    defn = s.definition()
                    sense_txt = f'{idx}.  {defn}'
                    tk.Label(inner, text=sense_txt, font=f_def, bg='white',
                             anchor='w', justify='left',
                             wraplength=340).pack(fill=tk.X, padx=(8, 0))

                    # Synonyms (other lemma names)
                    lemmas = [n.replace('_', ' ') for n in s.lemma_names()
                              if n.lower() != word.lower()]
                    if lemmas:
                        syn_txt = 'syn: ' + ',  '.join(lemmas)
                        tk.Label(inner, text=syn_txt, font=f_sub, fg='#336',
                                 bg='white', anchor='w', justify='left',
                                 wraplength=340).pack(fill=tk.X, padx=(20, 0))

                    # Examples
                    for ex in s.examples():
                        tk.Label(inner, text=f'"{ex}"', font=f_sub,
                                 fg='#555', bg='white', anchor='w',
                                 justify='left',
                                 wraplength=340).pack(fill=tk.X, padx=(20, 0))

                    tk.Frame(inner, height=4, bg='white').pack()   # spacer

        # Update scroll region once layout is complete
        inner.update_idletasks()
        cv.configure(scrollregion=cv.bbox('all'))

        tk.Button(popup, text='Close', command=popup.destroy).pack(pady=6)

    # ------------------------------------------------------------------ #
    # Dependency diagram (spaCy displacy)
    # ------------------------------------------------------------------ #

    def _diagram_click(self):
        if self._last_focus_row is None:
            messagebox.showinfo(
                "Diagram",
                "Click in your poem first, then press Diagram."
            )
            return
        text = self.lines[self._last_focus_row][0].get().strip()
        if not text:
            messagebox.showinfo("Diagram", "The current line is empty.")
            return
        if not _SPACY_AVAILABLE:
            messagebox.showerror(
                "Diagram",
                "spaCy is not installed.\nRun: pip install spacy && python -m spacy download en_core_web_md"
            )
            return
        if not _DIAGRAM_AVAILABLE:
            messagebox.showerror(
                "Diagram",
                "cairosvg and Pillow are required for the diagram.\nRun: pip install cairosvg Pillow"
            )
            return
        self._show_diagram_popup(text)

    def _show_diagram_popup(self, text):
        doc = self._get_spacy_doc(text)
        if doc is None:
            messagebox.showerror("Diagram", "Could not load spaCy model 'en_core_web_md'.")
            return

        options = {
            "compact": False,
            "bg":    "#fffef0",
            "color": "#003388",
            "fine_grained": True,
        }
        svg = _displacy.render(doc, style="dep", options=options)

        try:
            png_bytes = _cairosvg.svg2png(bytestring=svg.encode("utf-8"))
            img = _PILImage.open(_io.BytesIO(png_bytes))
        except Exception as exc:
            messagebox.showerror("Diagram", f"SVG render failed:\n{exc}")
            return

        popup = tk.Toplevel(self.root)
        popup.title("Dependency Diagram")
        popup.transient(self.root)
        popup.resizable(True, True)

        tk.Label(
            popup, text=text,
            font=("Helvetica", 11), wraplength=700,
            justify="left", pady=4,
        ).pack(fill=tk.X, padx=8)

        # ---- annotation row: POS / dep tags from spaCy ----
        info_frame = tk.Frame(popup, bg="#eef2fb")
        info_frame.pack(fill=tk.X, padx=8, pady=(0, 4))
        for tok in doc:
            if tok.is_alpha:
                cell = tk.Frame(info_frame, bg="#eef2fb", padx=4)
                cell.pack(side="left")
                tk.Label(cell, text=tok.text,  font=("Courier", 9, "bold"),
                         bg="#eef2fb").pack()
                tk.Label(cell, text=tok.dep_,  font=("Courier", 8),
                         fg="#005500", bg="#eef2fb").pack()
                tk.Label(cell, text=tok.pos_,  font=("Courier", 8),
                         fg="#550000", bg="#eef2fb").pack()
                if tok.ent_type_:
                    tk.Label(cell, text=f"[{tok.ent_type_}]",
                             font=("Courier", 7), fg="#884400",
                             bg="#eef2fb").pack()

        # ---- scrollable diagram canvas ----
        frame = tk.Frame(popup)
        frame.pack(fill=tk.BOTH, expand=True)

        h_sb = tk.Scrollbar(frame, orient="horizontal")
        v_sb = tk.Scrollbar(frame, orient="vertical")
        cv   = tk.Canvas(frame, bg="white",
                         xscrollcommand=h_sb.set, yscrollcommand=v_sb.set)
        h_sb.configure(command=cv.xview)
        v_sb.configure(command=cv.yview)
        h_sb.pack(side=tk.BOTTOM, fill=tk.X)
        v_sb.pack(side=tk.RIGHT, fill=tk.Y)
        cv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        photo = _PILImageTk.PhotoImage(img)
        cv.create_image(4, 4, anchor="nw", image=photo)
        cv._img_ref = photo  # prevent garbage collection
        cv.configure(scrollregion=(0, 0, img.width + 8, img.height + 8))

        def _scroll_x(event):
            cv.xview_scroll(int(-1 * (event.delta / 120)), "units")
        for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            cv.bind(seq, lambda e, s=cv: (
                s.yview_scroll(-1, "units") if e.num == 4
                else s.yview_scroll(1, "units") if e.num == 5
                else s.xview_scroll(int(-1 * (e.delta / 120)), "units")
            ))

        w = min(img.width + 30, self.root.winfo_screenwidth() - 100)
        h = min(img.height + 140, self.root.winfo_screenheight() - 100)
        popup.geometry(f"{w}x{h}")

        tk.Button(popup, text="Close", command=popup.destroy).pack(pady=6)

    # ------------------------------------------------------------------ #
    # Rhyme scheme column
    # ------------------------------------------------------------------ #

    def _rhyme_suffix(self, word):
        """Return the phoneme tuple from the last stressed vowel to the end.

        This is the phonological definition of the rhyming portion of a word.
        Two words are perfect rhymes iff their suffixes are equal (and non-empty).
        Falls back to None when the word is unknown to cmudict.
        """
        entry = self._best_cmu_entry(word)
        if not entry:
            return None
        # Walk backwards to find the last stressed vowel (digit marker)
        for i in range(len(entry) - 1, -1, -1):
            if entry[i][-1].isdigit():
                # Strip stress digits for comparison
                return tuple(re.sub(r'\d', '', ph) for ph in entry[i:])
        return None

    def _compute_rhyme_scheme(self):
        """Return a list of rhyme-scheme letters (one per line, '' for blank).

        Uses phoneme-suffix equality — the correct definition of perfect rhyme —
        so open-syllable words like 'day'/'may' (suffix: EY) are handled
        correctly, unlike the rdict prefix approach which requires identical
        trailing consonants.

        A–Z for the first 26 groups, then a–z.
        """
        scheme   = []
        # anchors: list of (rhyme_suffix_tuple, letter)
        anchors  = []
        next_idx = 0

        for te, _ in self.lines:
            words_in = re.findall(r'[A-Za-z]+', te.get())
            if not words_in:
                scheme.append('')
                continue

            suffix = self._rhyme_suffix(words_in[-1])

            letter = None
            if suffix:
                for anchor_suffix, anchor_letter in anchors:
                    if anchor_suffix == suffix:
                        letter = anchor_letter
                        break

            if letter is None:
                if next_idx < 26:
                    letter = chr(ord('A') + next_idx)
                else:
                    letter = chr(ord('a') + next_idx - 26)
                next_idx += 1
                if suffix:
                    anchors.append((suffix, letter))

            scheme.append(letter)

        return scheme

    def _update_rhyme_scheme(self):
        scheme = self._compute_rhyme_scheme()
        for i, letter in enumerate(scheme):
            if i >= len(self._rhyme_cells):
                break
            rc = self._rhyme_cells[i]
            rc.configure(state='normal')
            rc.delete(0, tk.END)
            if letter:
                rc.insert(0, letter)
            rc.configure(state='readonly')

    def _line_syllables(self, text):
        total = 0
        for token in word_tokenize(text):
            if not any(ch.isalpha() for ch in token):
                continue
            n = self._cmu_syllables(token)
            if n is None:
                n = self._fallback_syllables(token)
            total += n
        return total

    def _update_margin(self, row):
        count = self._line_syllables(self.lines[row][0].get())
        me = self.lines[row][1]
        me.configure(state="normal")
        me.delete(0, tk.END)
        if count:
            me.insert(0, str(count))
        me.configure(state="readonly")

    # ------------------------------------------------------------------ #
    # Meter: syllabification with stress levels
    # ------------------------------------------------------------------ #

    def _is_function(self, word, pos_tag, prev_word=None, dep=None):
        """Return True when word should be treated as prosodically weak.

        When a spaCy dependency label is supplied it takes precedence:
        dep='aux'  reliably marks auxiliaries; dep='ROOT' protects the main
        verb from being wrongly destressed by the _AUXILIARIES word list.
        Named-entity words (dep supplied as a non-empty ent marker via the
        caller) are always treated as stressed content words.
        """
        # spaCy dep labels: high-confidence structural function markers.
        if dep is not None:
            if dep == 'ROOT':
                return False   # main verb is always a content word
            if dep in _WEAK_DEPS:
                return True
        # POS-tag and word-list fallbacks (used when spaCy is unavailable).
        if pos_tag in _FUNCTION_POS:
            return True
        if word.lower() in _WEAK_WORDS:
            return True
        # Auxiliaries self-destress ("do GO", "hath MADE" — do/hath are weak).
        if word.lower() in _AUXILIARIES:
            return True
        # Participle after a have-type auxiliary is destressed (perfect aspect):
        # "hath made", "has gone", "had seen".
        # Be-type passive ("was MADE", "is SEEN") keeps the participle stressed.
        if (pos_tag in ('VBN', 'VBD') and prev_word
                and prev_word.lower() in _HAVE_AUX):
            return True
        return False

    def _syllabify_word(self, word, is_function=False):
        """Return [(syllable_text, stress), ...].
        stress: 0 = unstressed, 1 = primary, 2 = secondary.

        When is_function is True the word is treated as prosodically weak:
          1. Scan every cmudict entry for one whose vowel phonemes are all
             stress-0 (the reduced spoken form).  e.g. "for" has F AO1 R
             (citation) and F ER0 (reduced); "of" has AH1 V and AH0 V.
          2. If no all-zero entry exists:
             - Monosyllabic words: force stress-0 (no inherent stress peak).
             - Polysyllabic words: use primary pronunciation unchanged.
               "because" (B IH0 K AO1 Z) is IN but has an inherent stress
               peak on "-CAUSE" that must be preserved.
        Content words always use entries[0] (primary pronunciation).

        Syllable text uses equal character division, which outperforms
        vowel-onset splitting for English coda consonants:
            sighing    onset → si·ghing    equal → sigh·ing  ✓
            gentle     onset → ge·ntle     equal → gen·tle   ✓
            whispering onset → whi·spe·ring  equal → whis·per·ing  ✓
        """
        lower   = word.lower()
        entries = self._cmu.get(lower)

        if entries:
            best    = self._best_cmu_entry(lower)
            primary = [int(ph[-1]) for ph in best if ph[-1].isdigit()]
            if is_function and len(primary) == 1:
                # Monosyllabic function word: scan for an all-zero reduced form
                # ("for" → F ER0, "of" → AH0 V).  If none, force stress to 0.
                stresses = None
                for entry in entries:
                    s = [int(ph[-1]) for ph in entry if ph[-1].isdigit()]
                    if s and max(s) == 0:
                        stresses = s
                        break
                if stresses is None:
                    stresses = [0]
            else:
                # Polysyllabic words (even function-tagged ones like "because")
                # and all content words use the primary cmudict pronunciation.
                # Scanning for reduced forms of polysyllabic function words is
                # wrong — "because" has a casual entry B IH0 K AH0 Z that
                # would erase its inherent "-CAUSE" stress peak.
                stresses = primary
        else:
            stresses = [0] * max(1, self._fallback_syllables(lower))

        n = max(1, len(stresses))

        # Equal-length character division — all chars preserved, no chunk empty.
        wlen = len(word)
        base, rem = divmod(wlen, n)
        chunks, cursor = [], 0
        for k in range(n):
            size = base + (1 if k < rem else 0)
            chunks.append(word[cursor:cursor + size])
            cursor += size

        return [(chunks[k], stresses[k] if k < len(stresses) else 0)
                for k in range(n)]

    def _load_spacy_background(self):
        """Load the spaCy model in a background thread."""
        if not _SPACY_AVAILABLE or self._spacy_nlp is not None or self._spacy_loading:
            return
        self._spacy_loading = True
        try:
            self._spacy_nlp = _spacy.load("en_core_web_md")
        except Exception:
            pass
        finally:
            self._spacy_loading = False

    def _get_spacy_doc(self, text):
        """Return a spaCy Doc for text, loading the model lazily. None if unavailable."""
        if not _SPACY_AVAILABLE:
            return None
        if self._spacy_nlp is None:
            if self._spacy_loading:
                return None
            try:
                self._spacy_nlp = _spacy.load("en_core_web_md")
            except Exception:
                return None
        return self._spacy_nlp(text)

    def _tag_line(self, text):
        """Tag every word token; return list of (word, pos_tag, dep_label).

        Uses spaCy when available — dep labels improve function-word detection
        (e.g. dep='aux' reliably catches auxiliaries; dep='ROOT' protects the
        main verb; named entities are flagged as stressed content words).
        Falls back to NLTK pos_tag with empty dep strings.
        """
        word_tokens = re.findall(r'[A-Za-z]+', text)
        if not word_tokens:
            return []

        doc = self._get_spacy_doc(text)
        if doc is not None:
            result = []
            for tok in doc:
                if tok.is_alpha:
                    result.append((tok.text, tok.tag_, tok.dep_))
            if result:
                return result

        # NLTK fallback
        try:
            tagged = nltk.pos_tag(word_tokens)
        except Exception:
            tagged = [(w, "NN") for w in word_tokens]
        return [(w, tag, '') for w, tag in tagged]

    def _compose_meter_line_nltk(self, text):
        """
        Compose the full meter display string for a line (NLTK/CMUdict fallback).
        Stress shown by case: UPPERCASE=primary, Capitalized=secondary, lower=unstressed.
        Uses spaCy dep labels when available for more accurate function-word detection.
        """
        tagged    = self._tag_line(text)   # [(word, pos_tag, dep), ...]
        tag_iter  = iter(tagged)
        sep       = SEP_DOT
        parts     = []
        prev_word = None
        for token in re.split(r'([A-Za-z]+)', text):
            if not token:
                continue
            if re.match(r'[A-Za-z]+$', token):
                _, pos_tag, dep = next(tag_iter, (token, "NN", ""))
                func_flag = self._is_function(token, pos_tag, prev_word, dep or None)
                sylls = self._syllabify_word(token, func_flag)
                rendered = []
                for stext, stress in sylls:
                    if stress == 1:   rendered.append(stext.upper())
                    elif stress == 2: rendered.append(stext.capitalize())
                    else:             rendered.append(stext.lower())
                parts.append(sep.join(rendered))
                prev_word = token
            else:
                parts.append(token)
        return "".join(parts)

    def _compose_meter_line_prosodic(self, text):
        """Use prosodic for metrically-informed stress analysis.

        Returns None if prosodic is unavailable or parsing fails."""
        if not _PROSODIC_AVAILABLE or not text.strip():
            return None
        t = _prosodic.Text(text)
        t.parse()
        if not t.lines:
            return None
        line = t.lines[0]
        bp = line.best_parse
        if bp is None:
            return None

        slots = [s for s in bp.slots if s.syll is not None]
        slot_idx = 0
        parts = []

        for wt in line.get_list('WordToken'):
            word_txt  = wt.txt
            word_core = word_txt.strip()
            leading   = word_txt[: len(word_txt) - len(word_core)]
            if leading:
                parts.append(leading)
            if not word_core or not any(c.isalpha() for c in word_core):
                parts.append(word_core)
                continue

            target_len = len(re.sub(r"[^a-z']+", '', word_core.lower()))
            accumulated = 0
            word_slots  = []
            while slot_idx < len(slots) and accumulated < target_len:
                stxt        = slots[slot_idx].syll.txt
                accumulated += len(re.sub(r"[^a-z']+", '', stxt.lower()))
                word_slots.append(slots[slot_idx])
                slot_idx += 1

            rendered = [
                slot.syll.txt.upper() if slot.meter_val == 's' else slot.syll.txt.lower()
                for slot in word_slots
            ]
            parts.append(SEP_DOT.join(rendered))

        result = "".join(parts)
        return result if result else None

    def _compose_meter_line(self, text):
        """Compose the meter display string, preferring prosodic over NLTK."""
        try:
            result = self._compose_meter_line_prosodic(text)
            if result is not None:
                return result
        except Exception:
            pass
        return self._compose_meter_line_nltk(text)

    def _make_meter_widget(self, row):
        return tk.Text(
            self.inner,
            height=1,
            wrap=tk.NONE,
            relief="flat",
            bd=0,
            bg="#f7f3ec",
            highlightthickness=0,
            cursor="arrow",
            state="disabled",
            font=self._font_spec(),
        )

    def _fill_meter_widget(self, mt, text):
        line = self._compose_meter_line(text)
        mt.configure(state="normal", font=self._font_spec())
        mt.delete("1.0", tk.END)
        mt.insert("1.0", line)
        mt.configure(state="disabled")

    # ------------------------------------------------------------------ #
    # Meter toggle
    # ------------------------------------------------------------------ #

    def _ensure_meter_rows(self):
        while len(self._meter_rows) < len(self.lines):
            self._meter_rows.append(self._make_meter_widget(len(self._meter_rows)))

    def _show_meter(self):
        # Phase 1 (immediate): show empty meter rows so the UI layout appears.
        self._ensure_meter_rows()
        for i, (te, _) in enumerate(self.lines):
            te.grid_remove()
            self._meter_rows[i].grid(row=i, column=0, sticky="ew")
        # Phase 2 (background): compute meter strings per line and populate.
        if getattr(self, '_meter_loading', False):
            return  # worker already running
        self._meter_loading = True
        self._meter_worker = _MeterWorker(self)
        self._meter_worker.start()

    def _update_meter_line(self, index, meter_text):
        """Called by _MeterWorker from the main thread via after()."""
        if not self._meter_loading:
            return
        if index < len(self._meter_rows) and index < len(self.lines):
            self._fill_meter_widget(self._meter_rows[index], meter_text or '')

    def _meter_done(self):
        self._meter_loading = False

    def _hide_meter(self):
        # If background computation is running, stop updating.
        self._meter_loading = False
        for i, (te, _) in enumerate(self.lines):
            if i < len(self._meter_rows):
                self._meter_rows[i].grid_remove()
            te.grid(row=i, column=0, sticky="ew")

    def _toggle_meter(self):
        if self._meter_var.get():
            self._show_meter()
        else:
            self._hide_meter()

    # ------------------------------------------------------------------ #
    # UI construction
    # ------------------------------------------------------------------ #

    def _build_ui(self):
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=0)   # toolbar
        self.root.rowconfigure(1, weight=1)   # editor

        # --- Toolbar ---
        tb = tk.Frame(self.root, bd=1, relief="raised")
        tb.grid(row=0, column=0, sticky="ew")

        # Meter toggle button (Checkbutton with indicatoron=False acts as a push-toggle)
        self._meter_btn = tk.Checkbutton(
            tb, text="Meter",
            variable=self._meter_var,
            command=self._toggle_meter,
            indicatoron=False,
            relief="raised",
            padx=8, pady=2,
        )
        self._meter_btn.pack(side="left", padx=6, pady=3)

        tk.Button(
            tb, text="Rhyme", command=self._rhyme_click,
            relief="raised", padx=8, pady=2,
        ).pack(side="left", padx=(0, 6), pady=3)

        # Lookup field — revealed when Rhyme is clicked with no poem focus
        self._rhyme_input_var = tk.StringVar()
        self._rhyme_input = tk.Entry(tb, textvariable=self._rhyme_input_var, width=15)
        self._rhyme_input.bind("<Return>", self._rhyme_lookup_from_field)
        # Not packed yet; shown on demand

        tk.Button(
            tb, text="Definition", command=self._definition_click,
            relief="raised", padx=8, pady=2,
        ).pack(side="left", padx=(0, 6), pady=3)

        tk.Button(
            tb, text="Diagram", command=self._diagram_click,
            relief="raised", padx=8, pady=2,
        ).pack(side="left", padx=(0, 6), pady=3)

        tk.Button(
            tb, text="Thesaurus", command=self._thesaurus_click,
            relief="raised", padx=8, pady=2,
        ).pack(side="left", padx=(0, 6), pady=3)

        # Spacer to push right-side buttons
        tk.Frame(tb).pack(side="left", fill="x", expand=True)

        tk.Button(
            tb, text="About", command=self._about_click,
            relief="raised", padx=8, pady=2,
        ).pack(side="right", padx=6, pady=3)

        tk.Button(
            tb, text="Version", command=self._version_click,
            relief="raised", padx=8, pady=2,
        ).pack(side="right", padx=(0, 6), pady=3)

        tk.Button(
            tb, text="Tree", command=self._tree_click,
            relief="raised", padx=8, pady=2,
        ).pack(side="right", padx=(0, 6), pady=3)

        # --- Editor area ---
        outer = tk.Frame(self.root)
        outer.grid(row=1, column=0, sticky="nsew")
        outer.columnconfigure(0, weight=1)
        outer.rowconfigure(0, weight=1)

        self.canvas = tk.Canvas(outer, bg="white", highlightthickness=0)
        vscroll = tk.Scrollbar(outer, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=vscroll.set)
        self.canvas.grid(row=0, column=0, sticky="nsew")
        vscroll.grid(row=0, column=1, sticky="ns")

        self.inner = tk.Frame(self.canvas, bg="white")
        self._win  = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
        self.inner.columnconfigure(0, weight=1)
        self.inner.columnconfigure(1, weight=0, minsize=self._char_w * MARGIN_CHARS)
        self.inner.columnconfigure(2, weight=0, minsize=self._char_w)

        self.inner.bind("<Configure>",
                        lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.bind("<Configure>", self._on_canvas_resize)
        for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.canvas.bind(seq, self._scroll)
        # Global drag/release bindings using bind_all so they fire BEFORE
        # entry widget bindings. This lets us intercept the drag and either
        # allow default text selection (return None) or override it for
        # multi-line row selection (return "break").
        self.root.bind_all("<B1-Motion>",       self._on_drag)
        self.root.bind_all("<ButtonRelease-1>", self._on_release)

        self._build_menu()

    def _build_menu(self):
        menu = tk.Menu(self.root)

        fm = tk.Menu(menu, tearoff=0)
        fm.add_command(label="New",      command=self._new)
        fm.add_command(label="Open…",    command=self._open)
        fm.add_separator()
        fm.add_command(label="New Repository (Enable Version Control)", command=self._new_repo)
        fm.add_command(label="Open Repository (Version Control)",       command=self._open_repo)
        fm.add_separator()
        fm.add_command(label="Save",     command=self._save)
        fm.add_command(label="Save As…", command=self._save_as)
        fm.add_separator()
        fm.add_command(label="Import…",  command=self._import)
        fm.add_command(label="Export…",  command=self._export)
        fm.add_separator()
        fm.add_command(label="Exit",     command=self._quit)
        menu.add_cascade(label="File", menu=fm)

        font_menu = tk.Menu(menu, tearoff=0)
        for fname in self._avail_fonts:
            font_menu.add_radiobutton(label=fname, variable=self._font_var,
                                      value=fname, command=self._apply_font)
        menu.add_cascade(label="Font", menu=font_menu)

        size_menu = tk.Menu(menu, tearoff=0)
        for sz in SIZES:
            size_menu.add_radiobutton(label=str(sz), variable=self._size_var,
                                      value=sz, command=self._apply_font)
        menu.add_cascade(label="Size", menu=size_menu)

        self.root.config(menu=menu)

    def _on_canvas_resize(self, event):
        self.canvas.itemconfig(self._win, width=event.width)

    def _scroll(self, event):
        if event.num == 4:
            self.canvas.yview_scroll(-1, "units")
        elif event.num == 5:
            self.canvas.yview_scroll(1, "units")
        else:
            self.canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")

    # ------------------------------------------------------------------ #
    # Row management
    # ------------------------------------------------------------------ #

    def _row_of(self, widget):
        """Return the row index for any widget in that row.

        Checks text entry, margin entry, and rhyme cell entry widgets.
        Uses path-name comparison since tkinter event.widget may be a string.
        """
        if widget is None:
            return None
        target = str(widget)
        for i, (te, me) in enumerate(self.lines):
            if str(te) == target or str(me) == target:
                return i
            if i < len(self._rhyme_cells) and str(self._rhyme_cells[i]) == target:
                return i
        return None

    def _bind_row(self, widget, event, handler, offset=0):
        """Bind an event to a handler that receives the widget's current row."""
        def wrapper(e):
            row = self._row_of(e.widget)
            if row is None:
                return "break"
            return handler(row + offset)
        widget.bind(event, wrapper)

    def _clear_row_selection(self):
        if self._sel_anchor is None:
            return
        start = min(self._sel_anchor, self._sel_focus)
        end   = max(self._sel_anchor, self._sel_focus)
        for i in range(start, end + 1):
            if i < len(self.lines):
                self.lines[i][0].configure(bg="white")
        self._sel_anchor = None
        self._sel_focus  = None
        self.root.update_idletasks()

    def _update_row_selection(self, anchor, focus):
        old_start = min(self._sel_anchor, self._sel_focus) if self._sel_anchor is not None else None
        old_end   = max(self._sel_anchor, self._sel_focus) if self._sel_anchor is not None else None

        self._sel_anchor = anchor
        self._sel_focus  = focus
        new_start = min(anchor, focus)
        new_end   = max(anchor, focus)

        # Clear rows that are no longer in the selection.
        if old_start is not None:
            for i in range(old_start, old_end + 1):
                if i < len(self.lines) and not (new_start <= i <= new_end):
                    self.lines[i][0].configure(bg="white")

        # Highlight rows in the new selection.
        for i in range(new_start, new_end + 1):
            if i < len(self.lines):
                te = self.lines[i][0]
                te.configure(bg="#cce5ff")
                try:
                    te.selection_clear()
                except tk.TclError:
                    pass

        self.root.update_idletasks()

    def _add_row(self, text=""):
        row  = len(self.lines)
        spec = self._font_spec()
        fname, fsize = spec

        te = tk.Entry(
            self.inner, font=spec, relief="flat", bd=0,
            bg="white", highlightthickness=0, insertbackground="black",
        )
        me = tk.Entry(
            self.inner, font=spec, relief="flat", bd=0,
            bg="#e8e8e8", highlightthickness=0,
            width=MARGIN_CHARS, justify="center",
            state="readonly", readonlybackground="#e8e8e8",
        )
        if text:
            te.insert(0, text)

        rc = tk.Entry(
            self.inner, font=spec, relief="flat", bd=0,
            bg="#dde8dd", highlightthickness=0,
            width=1, justify="center",
            state="readonly", readonlybackground="#dde8dd",
        )

        te.grid(row=row, column=0, sticky="ew")
        me.grid(row=row, column=1, sticky="ew")
        rc.grid(row=row, column=2, sticky="ew")

        def _kp(e):
            if e.keysym in ("Up", "Down") and (e.state & 0x1):
                r = self._row_of(e.widget)
                if r is None:
                    return "break"
                if e.keysym == "Up":
                    self._shift_up(r)
                else:
                    self._shift_down(r)
                return "break"
            return None
        te.bind("<KeyPress>", _kp)
        # Also bind specific keys to ensure they fire on all platforms.
        te.bind("<Shift-KeyPress-Up>", lambda e: self._shift_up(self._row_of(e.widget)) or "break")
        te.bind("<Shift-KeyPress-Down>", lambda e: self._shift_down(self._row_of(e.widget)) or "break")

        self._bind_row(te, "<KeyRelease>", self._on_key)
        self._bind_row(te, "<Return>",     self._next)
        self._bind_row(te, "<BackSpace>",  self._backspace)
        self._bind_row(te, "<Down>",       self._go, offset=1)
        self._bind_row(te, "<Up>",         self._go, offset=-1)
        self._bind_row(te, "<Tab>",        self._go, offset=1)
        self._bind_row(te, "<FocusIn>",    self._on_focus_in)
        self._bind_row(te, "<FocusOut>",   self._on_focus_out)
        self._bind_row(te, "<<Paste>>",    self._paste)
        self._bind_row(te, "<Control-c>",  self._copy)
        self._bind_row(te, "<Control-C>",  self._copy)
        self._bind_row(te, "<Command-c>",  self._copy)
        self._bind_row(te, "<Command-C>",  self._copy)
        self._bind_row(te, "<Control-x>",  self._cut)
        self._bind_row(te, "<Control-X>",  self._cut)
        self._bind_row(te, "<Command-x>",  self._cut)
        self._bind_row(te, "<Command-X>",  self._cut)
        self._bind_row(te, "<Shift-Up>",   self._shift_up)
        self._bind_row(te, "<Shift-Down>", self._shift_down)
        self._bind_row(te, "<Button-1>",   self._on_click)

        self._line_meta.append(
            [{"font": fname, "size": fsize, "len": len(text)}] if text else []
        )
        self._rhyme_cells.append(rc)
        self.lines.append((te, me))
        if text:
            self._update_margin(row)

    def _insert_row(self, row, text=""):
        """Insert a new line at the specified row index."""
        if row > len(self.lines):
            row = len(self.lines)

        spec = self._font_spec()
        fname, fsize = spec

        te = tk.Entry(
            self.inner, font=spec, relief="flat", bd=0,
            bg="white", highlightthickness=0, insertbackground="black",
        )
        me = tk.Entry(
            self.inner, font=spec, relief="flat", bd=0,
            bg="#e8e8e8", highlightthickness=0,
            width=MARGIN_CHARS, justify="center",
            state="readonly", readonlybackground="#e8e8e8",
        )
        if text:
            te.insert(0, text)

        rc = tk.Entry(
            self.inner, font=spec, relief="flat", bd=0,
            bg="#dde8dd", highlightthickness=0,
            width=1, justify="center",
            state="readonly", readonlybackground="#dde8dd",
        )

        self.lines.insert(row, (te, me))
        self._rhyme_cells.insert(row, rc)
        self._line_meta.insert(
            row, [{"font": fname, "size": fsize, "len": len(text)}] if text else []
        )

        if len(self._meter_rows) > 0:
            mt = self._make_meter_widget(row)
            self._meter_rows.insert(row, mt)
            if text:
                self._fill_meter_widget(mt, text)

        meter_on = self._meter_var.get()
        for i in range(row, len(self.lines)):
            te2, me2 = self.lines[i]
            if meter_on and i < len(self._meter_rows):
                te2.grid_remove()
                self._meter_rows[i].grid(row=i, column=0, sticky="ew")
            else:
                if i < len(self._meter_rows):
                    self._meter_rows[i].grid_remove()
                te2.grid(row=i, column=0, sticky="ew")
            me2.grid(row=i, column=1, sticky="ew")
            if i < len(self._rhyme_cells):
                self._rhyme_cells[i].grid(row=i, column=2, sticky="ew")

        def _kp(e):
            if e.keysym in ("Up", "Down") and (e.state & 0x1):
                r = self._row_of(e.widget)
                if r is None:
                    return "break"
                if e.keysym == "Up":
                    self._shift_up(r)
                else:
                    self._shift_down(r)
                return "break"
            return None
        te.bind("<KeyPress>", _kp)
        # Also bind specific keys to ensure they fire on all platforms.
        te.bind("<Shift-KeyPress-Up>", lambda e: self._shift_up(self._row_of(e.widget)) or "break")
        te.bind("<Shift-KeyPress-Down>", lambda e: self._shift_down(self._row_of(e.widget)) or "break")

        self._bind_row(te, "<KeyRelease>", self._on_key)
        self._bind_row(te, "<Return>",     self._next)
        self._bind_row(te, "<BackSpace>",  self._backspace)
        self._bind_row(te, "<Down>",       self._go, offset=1)
        self._bind_row(te, "<Up>",         self._go, offset=-1)
        self._bind_row(te, "<Tab>",        self._go, offset=1)
        self._bind_row(te, "<FocusIn>",    self._on_focus_in)
        self._bind_row(te, "<FocusOut>",   self._on_focus_out)
        self._bind_row(te, "<<Paste>>",    self._paste)
        self._bind_row(te, "<Control-c>",  self._copy)
        self._bind_row(te, "<Control-C>",  self._copy)
        self._bind_row(te, "<Command-c>",  self._copy)
        self._bind_row(te, "<Command-C>",  self._copy)
        self._bind_row(te, "<Control-x>",  self._cut)
        self._bind_row(te, "<Control-X>",  self._cut)
        self._bind_row(te, "<Command-x>",  self._cut)
        self._bind_row(te, "<Command-X>",  self._cut)
        self._bind_row(te, "<Shift-Up>",   self._shift_up)
        self._bind_row(te, "<Shift-Down>", self._shift_down)
        self._bind_row(te, "<Button-1>",   self._on_click)

    def _on_key(self, row):
        self._mark_dirty()
        self._update_margin(row)
        self._update_rhyme_scheme()
        if self._meter_var.get() and row < len(self._meter_rows):
            text = self.lines[row][0].get()
            self._fill_meter_widget(self._meter_rows[row], text)

    def _populate(self, n):
        for _ in range(n):
            self._add_row()

    def _next(self, row):
        self._clear_row_selection()
        te = self.lines[row][0]
        cursor = te.index(tk.INSERT)
        text = te.get()
        after = text[cursor:]
        if after:
            te.delete(cursor, tk.END)
            self._update_margin(row)
        if row + 1 >= len(self.lines):
            self._add_row(after)
        else:
            self._insert_row(row + 1, after)
        self.lines[row + 1][0].focus_set()
        self.lines[row + 1][0].icursor(0)
        self._update_rhyme_scheme()
        if self._meter_var.get():
            if row < len(self._meter_rows):
                self._fill_meter_widget(self._meter_rows[row], te.get())
            if row + 1 < len(self._meter_rows):
                self._fill_meter_widget(self._meter_rows[row + 1], after)
        return "break"

    def _go(self, row):
        self._clear_row_selection()
        if 0 <= row < len(self.lines):
            self.lines[row][0].focus_set()
        return "break"

    def _shift_up(self, row):
        if self._sel_anchor is None:
            self._sel_anchor = row
            self._sel_focus  = row
        new_focus = max(0, self._sel_focus - 1)
        self._update_row_selection(self._sel_anchor, new_focus)
        if 0 <= new_focus < len(self.lines):
            self.lines[new_focus][0].focus_set()
        return "break"

    def _shift_down(self, row):
        if self._sel_anchor is None:
            self._sel_anchor = row
            self._sel_focus  = row
        new_focus = min(len(self.lines) - 1, self._sel_focus + 1)
        self._update_row_selection(self._sel_anchor, new_focus)
        if 0 <= new_focus < len(self.lines):
            self.lines[new_focus][0].focus_set()
        return "break"

    def _on_click(self, row):
        # Record click row for distinguishing single-line vs multi-line drag.
        self._click_row = row
        te = self.lines[row][0]
        self._click_index = te.index(tk.INSERT)
        # Clear any existing row selection on new click.
        self._clear_row_selection()

    def _on_drag(self, event):
        try:
            widget_at = self.root.winfo_containing(event.x_root, event.y_root)
        except (tk.TclError, KeyError):
            return self._handle_drag_outside()
        if widget_at is None:
            return self._handle_drag_outside()
        row = self._row_of(widget_at)
        if row is None:
            return self._handle_drag_outside()
        if self._click_row is None:
            return "break"

        if row == self._click_row:
            if self._sel_anchor is not None:
                self._clear_row_selection()
            return "break"

        if self._sel_anchor is None:
            self._sel_anchor = self._click_row
            self._sel_focus  = self._click_row
        self._update_row_selection(self._sel_anchor, row)
        self.lines[row][0].focus_set()
        return "break"

    def _handle_drag_outside(self):
        """Handle drag when cursor is over a non-entry widget."""
        if self._sel_anchor is not None and self._click_row is not None:
            self._update_row_selection(self._sel_anchor, self._click_row)
            return "break"
        return "break"

    def _on_release(self, event):
        self._click_row = None
        self._click_index = None
        return None

    def _delete_row(self, row):
        """Remove a row and re-grid everything below it."""
        if row >= len(self.lines):
            return
        te, me = self.lines.pop(row)
        te.destroy()
        me.destroy()
        if row < len(self._rhyme_cells):
            self._rhyme_cells.pop(row).destroy()
        if row < len(self._meter_rows):
            self._meter_rows.pop(row).destroy()
        if row < len(self._line_meta):
            self._line_meta.pop(row)
        # Re-grid remaining rows so their grid row numbers stay correct,
        # respecting the current meter mode.
        meter_on = self._meter_var.get()
        for i in range(row, len(self.lines)):
            te2, me2 = self.lines[i]
            if meter_on and i < len(self._meter_rows):
                te2.grid_remove()
                self._meter_rows[i].grid(row=i, column=0, sticky="ew")
            else:
                if i < len(self._meter_rows):
                    self._meter_rows[i].grid_remove()
                te2.grid(row=i, column=0, sticky="ew")
            me2.grid(row=i, column=1, sticky="ew")
            if i < len(self._rhyme_cells):
                self._rhyme_cells[i].grid(row=i, column=2, sticky="ew")
        if self._last_focus_row is not None and self._last_focus_row >= len(self.lines):
            self._last_focus_row = None
            self._last_focus_cursor = 0

    def _backspace(self, row):
        te = self.lines[row][0]
        cursor = te.index(tk.INSERT)
        if cursor == 0 and row > 0:
            self._mark_dirty()
            self._clear_row_selection()
            text = te.get()
            self._delete_row(row)
            prev_row = row - 1
            prev_te = self.lines[prev_row][0]
            prev_len = len(prev_te.get())
            prev_te.insert(tk.END, text)
            prev_te.focus_set()
            prev_te.icursor(prev_len)
            self._update_margin(prev_row)
            self._update_rhyme_scheme()
            return "break"
        # Let the default BackSpace behavior happen
        return None

    def _copy(self, row):
        """Copy selected text, selected rows, or all lines."""
        # Multi-row selection takes priority.
        if self._sel_anchor is not None:
            self.root.clipboard_clear()
            start = min(self._sel_anchor, self._sel_focus)
            end   = max(self._sel_anchor, self._sel_focus)
            lines = [self.lines[i][0].get() for i in range(start, end + 1)
                     if i < len(self.lines)]
            self.root.clipboard_append("\n".join(lines))
            return "break"
        te = self.lines[row][0]
        try:
            if te.selection_present():
                self.root.clipboard_clear()
                self.root.clipboard_append(te.selection_get())
                return "break"
        except tk.TclError:
            pass
        # No selection at all — copy the entire poem.
        self.root.clipboard_clear()
        self.root.clipboard_append("\n".join(line.get() for line, _ in self.lines))
        return "break"

    def _cut(self, row):
        """Cut selected text, selected rows, or do nothing."""
        # Multi-row selection takes priority.
        if self._sel_anchor is not None:
            self.root.clipboard_clear()
            start = min(self._sel_anchor, self._sel_focus)
            end   = max(self._sel_anchor, self._sel_focus)
            lines = [self.lines[i][0].get() for i in range(start, end + 1)
                     if i < len(self.lines)]
            self.root.clipboard_append("\n".join(lines))
            # Delete selected rows (keep at least one row).
            self._mark_dirty()
            for i in range(end, start - 1, -1):
                if len(self.lines) > 1:
                    self._delete_row(i)
            self._sel_anchor = None
            self._sel_focus = None
            # Ensure at least one row exists
            if not self.lines:
                self._add_row()
            self._update_rhyme_scheme()
            return "break"
        te = self.lines[row][0]
        try:
            if te.selection_present():
                self.root.clipboard_clear()
                self.root.clipboard_append(te.selection_get())
                te.delete(tk.SEL_FIRST, tk.SEL_LAST)
                self._mark_dirty()
                self._update_margin(row)
                if self._meter_var.get() and row < len(self._meter_rows):
                    self._fill_meter_widget(self._meter_rows[row], te.get())
                self._update_rhyme_scheme()
                return "break"
        except tk.TclError:
            pass
        return "break"

    def _paste(self, row):
        """Handle multi-line paste by splitting on universal newlines."""
        # Save multi-line selection state before clearing.
        had_multi_sel = self._sel_anchor is not None
        if had_multi_sel:
            sel_start = min(self._sel_anchor, self._sel_focus)
            sel_end   = max(self._sel_anchor, self._sel_focus)
        self._clear_row_selection()
        try:
            clip = self.root.clipboard_get()
        except tk.TclError:
            return "break"
        lines = clip.splitlines()
        if not lines:
            return "break"
        self._mark_dirty()

        # If multiple lines were selected, replace them with pasted content.
        if had_multi_sel:
            # Delete selected rows first
            for i in range(sel_end, sel_start - 1, -1):
                if len(self.lines) > 1:
                    self._delete_row(i)
                else:
                    # If only one row remains, clear it instead of deleting
                    if sel_start < len(self.lines):
                        te = self.lines[sel_start][0]
                        te.delete(0, tk.END)

            # Now insert pasted content starting at the selection start row.
            current_row = sel_start
            for i, line in enumerate(lines):
                if current_row >= len(self.lines):
                    self._add_row()
                    if self._meter_var.get():
                        self._ensure_meter_rows()
                te = self.lines[current_row][0]
                te.delete(0, tk.END)
                te.insert(0, line)
                self._update_margin(current_row)
                current_row += 1

            # Focus the last pasted row
            last_row = current_row - 1
            if last_row >= len(self.lines):
                last_row = len(self.lines) - 1
            self.lines[last_row][0].focus_set()
            self.lines[last_row][0].icursor(tk.END)
            self._update_rhyme_scheme()
            if self._meter_var.get():
                for r in range(sel_start, current_row):
                    if r < len(self._meter_rows):
                        text = self.lines[r][0].get()
                        self._fill_meter_widget(self._meter_rows[r], text)
            return "break"

        # No multi-line selection: original behavior (insert at cursor).
        current_row = row
        for i, line in enumerate(lines):
            if current_row >= len(self.lines):
                self._add_row()
                if self._meter_var.get():
                    self._ensure_meter_rows()
            te = self.lines[current_row][0]
            if i == 0:
                # First line: insert at current cursor position
                te.insert(tk.INSERT, line)
            else:
                # Subsequent lines: replace entire row content
                te.delete(0, tk.END)
                te.insert(0, line)
            self._update_margin(current_row)
            current_row += 1
        # Focus the last row with cursor at end
        last_row = current_row - 1
        self.lines[last_row][0].focus_set()
        self.lines[last_row][0].icursor(tk.END)
        self._update_rhyme_scheme()
        if self._meter_var.get():
            for r in range(row, current_row):
                if r < len(self._meter_rows):
                    text = self.lines[r][0].get()
                    self._fill_meter_widget(self._meter_rows[r], text)
        return "break"

    def _trim_rows(self, target):
        """Destroy excess rows and their associated widgets to prevent leaks."""
        while len(self.lines) > target:
            row = len(self.lines) - 1
            te, me = self.lines.pop()
            te.destroy()
            me.destroy()
            if row < len(self._rhyme_cells):
                self._rhyme_cells[row].destroy()
            if row < len(self._meter_rows):
                self._meter_rows[row].destroy()
            if row < len(self._line_meta):
                self._line_meta.pop()
        # Clean up trailing rhyme cells / meter rows that may exceed line count
        while len(self._rhyme_cells) > len(self.lines):
            self._rhyme_cells.pop().destroy()
        while len(self._meter_rows) > len(self.lines):
            self._meter_rows.pop().destroy()
        while len(self._line_meta) > len(self.lines):
            self._line_meta.pop()
        if self._last_focus_row is not None and self._last_focus_row >= len(self.lines):
            self._last_focus_row = None
            self._last_focus_cursor = 0

    # ------------------------------------------------------------------ #
    # Meta file
    # ------------------------------------------------------------------ #

    def _build_meta(self):
        return {
            "version": 1,
            "font":  self._font_var.get(),
            "size":  self._size_var.get(),
            "lines": [self._runs_for_line(i) for i in range(len(self.lines))],
        }

    def _apply_meta(self, meta):
        fname = meta.get("font", DEFAULT_FONT)
        fsize = meta.get("size", DEFAULT_SIZE)
        if fname in self._avail_fonts:
            self._font_var.set(fname)
        self._size_var.set(fsize)
        for i, runs in enumerate(meta.get("lines", [])):
            if i < len(self._line_meta):
                self._line_meta[i] = runs
        self._apply_font()

    # ------------------------------------------------------------------ #
    # Dirty-state tracking and unsaved-changes guard
    # ------------------------------------------------------------------ #

    def _update_title(self):
        name  = os.path.basename(self._current_path) if self._current_path else "Untitled"
        dirty = " \u2022" if self._is_dirty else ""   # bullet = unsaved indicator
        self.root.title(f"{name}{dirty} — Poedit")

    def _mark_dirty(self):
        if not self._is_dirty:
            self._is_dirty = True
            self._update_title()

    def _mark_clean(self):
        self._is_dirty = False
        self._update_title()

    def _confirm_discard(self):
        """Return True if it is safe to replace the current document.

        When there are unsaved changes, shows a three-way dialog:
          Yes    → save (or Save As if no path), then return True
          No     → discard changes, return True
          Cancel → return False (caller should abort)
        """
        if not self._is_dirty:
            return True
        name   = os.path.basename(self._current_path) if self._current_path else "Untitled"
        answer = messagebox.askyesnocancel(
            "Unsaved Changes",
            f'"{name}" has unsaved changes.\n\nSave before continuing?',
        )
        if answer is None:      # Cancel
            return False
        if answer:              # Yes — save first
            try:
                if self._current_path:
                    self._write_files(self._current_path)
                else:
                    path = filedialog.asksaveasfilename(
                        defaultextension=".txt",
                        filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")],
                    )
                    if not path:
                        return False    # user cancelled the Save As dialog
                    self._write_files(path)
            except Exception:
                return False        # save failed; abort to avoid data loss
        return True             # No — discard and proceed

    def _new(self):
        if not self._confirm_discard():
            return
        # Reset meter before trimming so hidden widgets don't leak
        if self._meter_var.get():
            self._meter_var.set(False)
            self._hide_meter()
        self._trim_rows(0)
        self._populate(INITIAL_LINES)
        self._current_path = None
        self._is_dirty     = False
        self._last_focus_row = None
        self._last_focus_cursor = 0
        self._update_rhyme_scheme()
        self._update_title()
        if self.lines:
            self.lines[0][0].focus_set()

    def _quit(self):
        if self._confirm_discard():
            self.root.quit()

    # ------------------------------------------------------------------ #
    # File I/O
    # ------------------------------------------------------------------ #

    def _load_file(self, path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                file_lines = f.read().splitlines()
        except Exception as exc:
            messagebox.showerror("Open Error", f"Could not open file:\n{exc}")
            return

        while len(self.lines) < max(len(file_lines), INITIAL_LINES):
            self._add_row()
        self._trim_rows(max(len(file_lines), INITIAL_LINES))

        for i, (te, me) in enumerate(self.lines):
            te.delete(0, tk.END)
            self._line_meta[i] = []
            me.configure(state="normal")
            me.delete(0, tk.END)
            me.configure(state="readonly")

        for i, text in enumerate(file_lines):
            self.lines[i][0].insert(0, text)

        mp = _meta_path(path)
        if os.path.exists(mp):
            try:
                with open(mp, "r", encoding="utf-8") as f:
                    self._apply_meta(json.load(f))
            except Exception:
                pass
        else:
            fname, fsize = self._font_var.get(), self._size_var.get()
            for i, text in enumerate(file_lines):
                self._line_meta[i] = (
                    [{"font": fname, "size": fsize, "len": len(text)}] if text else []
                )

        for i in range(len(file_lines)):
            self._update_margin(i)

        self._update_rhyme_scheme()

        if self._meter_var.get():
            self._show_meter()

        self._current_path = path
        self._mark_clean()

    def _write_files(self, path):
        content = [te.get() for te, _ in self.lines]
        while content and not content[-1]:
            content.pop()
        try:
            # Atomic write for text file
            fd, tmp = tempfile.mkstemp(dir=os.path.dirname(path) or ".", suffix=".tmp")
            try:
                with os.fdopen(fd, "w", encoding="utf-8") as f:
                    f.write("\n".join(content) + "\n")
                os.replace(tmp, path)
            except Exception:
                os.unlink(tmp)
                raise
            # Atomic write for meta file
            meta = self._build_meta()
            meta["lines"] = meta["lines"][:len(content)]
            meta_path = _meta_path(path)
            fd2, tmp2 = tempfile.mkstemp(dir=os.path.dirname(meta_path) or ".", suffix=".tmp")
            try:
                with os.fdopen(fd2, "w", encoding="utf-8") as f:
                    json.dump(meta, f, indent=2)
                os.replace(tmp2, meta_path)
            except Exception:
                os.unlink(tmp2)
                raise
            self._current_path = path
            self._mark_clean()
        except Exception as exc:
            messagebox.showerror("Save Error", f"Could not save file:\n{exc}")
            raise

    def _open(self):
        if not self._confirm_discard():
            return
        # If a repo is open, offer repo file selection first
        if getattr(self, "_repo_path", None) and os.path.exists(self._repo_path):
            self._show_repo_browser(self._repo_path)
            return
        # Otherwise check if user wants to configure version control
        path = filedialog.askopenfilename(
            filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")]
        )
        if path:
            self._load_file(path)

    def _save(self):
        if self._current_path:
            self._write_files(self._current_path)
        else:
            self._save_as()

    def _save_as(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")],
        )
        if path:
            self._write_files(path)

    def _import(self):
        """Import a poem file by full canonical path into the current repo."""
        if not self._confirm_discard():
            return
        if not self._ensure_repo_for_import_export():
            return
        path = filedialog.askopenfilename(
            title="Import Poem File",
            filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")],
        )
        if not path:
            return
        # Copy into repo
        dest = os.path.join(self._repo_path, os.path.basename(path))
        if os.path.exists(dest):
            base, ext = os.path.splitext(dest)
            n = 1
            while os.path.exists(f"{base}-{n}{ext}"):
                n += 1
            dest = f"{base}-{n}{ext}"
        try:
            import shutil
            shutil.copy2(path, dest)
            self._load_file(dest)
            self._do_commit_and_stage(f"Import: {os.path.basename(path)}")
            self._update_title()
        except Exception as exc:
            messagebox.showerror("Import Error", f"Could not import file:\n{exc}")

    def _export(self):
        """Export the current poem to a canonical path outside the repo."""
        if not self._current_path:
            messagebox.showinfo("Export", "Nothing to export — open or create a poem first.")
            return
        if not self._ensure_repo_for_import_export():
            return
        dest = filedialog.asksaveasfilename(
            title="Export Poem File",
            defaultextension=".txt",
            filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")],
        )
        if not dest:
            return
        try:
            import shutil
            # Save current state to repo first
            self._write_files(self._current_path)
            shutil.copy2(self._current_path, dest)
            meta_src = _meta_path(self._current_path)
            meta_dst = _meta_path(dest)
            if os.path.exists(meta_src):
                shutil.copy2(meta_src, meta_dst)
            messagebox.showinfo("Export", f"Exported to:\n{dest}")
        except Exception as exc:
            messagebox.showerror("Export Error", f"Could not export file:\n{exc}")

    def _ensure_repo_for_import_export(self):
        """Ensure a repo exists; if not, prompt to create one. Returns True if repo is ready."""
        if getattr(self, "_repo_path", None) and os.path.exists(self._repo_path):
            return True
        answer = messagebox.askyesno(
            "No Repository",
            "Import and Export require a repository.\n\n"
            "Would you like to create one now?",
        )
        if not answer:
            return False
        # Inline repo creation — reuse _new_repo logic but non-destructively
        popup = tk.Toplevel(self.root)
        popup.title("Create Repository")
        popup.transient(self.root)
        popup.resizable(False, False)
        popup.grab_set()

        tk.Label(popup, text="Repository name:").pack(anchor="w", padx=12, pady=(10, 2))
        name_var = tk.StringVar(value="poetry")
        name_entry = tk.Entry(popup, textvariable=name_var, width=40)
        name_entry.pack(anchor="w", padx=12)
        name_entry.focus_set()
        name_entry.select_range(0, tk.END)

        tk.Label(popup, text="Location:").pack(anchor="w", padx=12, pady=(8, 2))
        path_var = tk.StringVar(value=os.path.join(os.path.expanduser("~"), "Documents"))
        path_frame = tk.Frame(popup)
        path_frame.pack(anchor="w", padx=12)
        tk.Entry(path_frame, textvariable=path_var, width=32).pack(side="left")
        tk.Button(
            path_frame, text="Browse\u2026",
            command=lambda: _browse(),
        ).pack(side="left", padx=(4, 0))

        def _browse():
            d = filedialog.askdirectory(
                title="Select Parent Directory",
                initialdir=path_var.get() or os.path.expanduser("~"),
            )
            if d:
                path_var.set(d)

        result = {"ok": False}

        def _do_create():
            name = name_var.get().strip()
            base = path_var.get().strip()
            if not name:
                messagebox.showwarning("Error", "Repository name is required.")
                return
            if not base:
                messagebox.showwarning("Error", "Location is required.")
                return
            repo_dir = os.path.join(base, name)
            if os.path.exists(repo_dir):
                # If it's already a valid git repo, reuse it
                try:
                    Repo(repo_dir).close()
                    self._repo_path = repo_dir
                    self._save_repo_state(repo_dir)
                    result["ok"] = True
                    popup.destroy()
                    return
                except _dulwich_errors.NotGitRepository:
                    messagebox.showerror("Error", f"Directory already exists and is not a Git repo:\n{repo_dir}")
                    return
            os.makedirs(repo_dir)
            try:
                Repo.init(repo_dir)
                self._repo_path = repo_dir
                self._save_repo_state(repo_dir)
                result["ok"] = True
                popup.destroy()
            except Exception as exc:
                messagebox.showerror("Error", f"Could not create repository:\n{exc}")

        tk.Button(popup, text="Create Repository", command=_do_create).pack(pady=12)
        name_entry.bind("<Return>", lambda e: _do_create())

        popup.wait_window()
        return result.get("ok", False)


def main():
    root = tk.Tk()
    root.withdraw()

    splash = tk.Toplevel(root)
    splash.overrideredirect(True)

    # Load splash image.
    _splash_img = None
    img_path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            '..', 'ICD9N.jpg')
    if not os.path.exists(img_path):
        img_path = os.path.join(os.getcwd(), 'ICD9N.jpg')
    if os.path.exists(img_path):
        try:
            from PIL import Image as _PILImage, ImageTk as _PILImageTk
            _splash_img = _PILImageTk.PhotoImage(
                _PILImage.open(img_path).resize((480, 320), _PILImage.LANCZOS),
                master=splash)
        except Exception:
            _splash_img = None

    # Layout: image on top, status + bar below.
    if _splash_img:
        tk.Label(splash, image=_splash_img, bg="black").pack()
    else:
        tk.Label(splash, text="Poedit", font=("Courier", 28, "bold"),
                 fg="#c9a84c", bg="#1a1a1a", width=40, height=10).pack()

    status_var = tk.StringVar(value="Initializing…")
    tk.Label(splash, textvariable=status_var, font=("Courier", 10),
             bg="#1a1a1a", fg="#e0d8c0", anchor="w").pack(fill="x", padx=12, pady=(6, 2))

    style = ttk.Style()
    style.theme_use('clam')
    style.configure("splash.Horizontal.TProgressbar",
                     troughcolor="#333", background="#c9a84c", thickness=14)
    progress = ttk.Progressbar(splash, length=480, mode='determinate',
                                maximum=100, style="splash.Horizontal.TProgressbar")
    progress.pack(padx=12, pady=(0, 10))

    # Center and force the splash visible before any loading starts.
    splash.update_idletasks()
    sw = splash.winfo_screenwidth()
    sh = splash.winfo_screenheight()
    w  = splash.winfo_width()
    h  = splash.winfo_height()
    splash.geometry(f"+{(sw - w) // 2}+{(sh - h) // 2}")
    splash.update()   # paint splash now — before the background thread starts

    # --- Background loading thread ---
    _loaded = {}   # filled by worker; read by poll callback on main thread

    def _load_worker():
        _loaded['status'] = "Loading NLTK data…"
        _ensure_nltk_data()
        _loaded['progress'] = 20
        _loaded['status'] = "Loading CMU dictionary…"
        _loaded['cmu']     = cmudict.dict()
        _loaded['syl_tok'] = SyllableTokenizer()
        _loaded['progress'] = 45
        _loaded['status'] = "Loading rhyme dictionary…"
        _loaded['rhyme_dict'] = Editor._load_rhyme_dict_static()
        _loaded['progress'] = 65
        if _PROSODIC_AVAILABLE:
            _loaded['status'] = "Warming up meter analysis…"
            try:
                # Trigger any lazy NLTK downloads prosodic needs on first parse.
                _prosodic.Text("the quick brown fox").parse()
            except Exception:
                pass
        _loaded['progress'] = 85
        _loaded['status'] = "Building UI…"
        _loaded['done'] = True

    threading.Thread(target=_load_worker, daemon=True).start()

    # Poll every 40 ms; update the splash from the main thread.
    def _poll():
        if 'status' in _loaded:
            status_var.set(_loaded.pop('status'))
        if 'progress' in _loaded:
            progress['value'] = _loaded.pop('progress')
        if not _loaded.get('done'):
            root.after(40, _poll)
            return
        progress['value'] = 100
        splash.update()
        Editor(root, _preloaded=dict(
            cmu=_loaded['cmu'],
            syl_tok=_loaded['syl_tok'],
            rhyme_dict=_loaded['rhyme_dict'],
        ))
        splash.destroy()
        root.deiconify()

    root.after(40, _poll)
    root.mainloop()


if __name__ == "__main__":
    main()
