import json
import os
import re
import threading

import nltk
from nltk import word_tokenize
from nltk.tokenize import SyllableTokenizer

try:
    import prosodic as _prosodic
    _PROSODIC_AVAILABLE = True
except ImportError:
    _PROSODIC_AVAILABLE = False

try:
    import spacy as _spacy
    SPACY_AVAILABLE = True
except ImportError:
    SPACY_AVAILABLE = False

SEP_DOT = "·"

_WEAK_DEPS = frozenset({
    'aux', 'auxpass', 'det', 'mark', 'cc', 'case', 'expl', 'prep',
})

_FUNCTION_POS = frozenset({
    "CC", "DT", "EX", "IN", "MD", "PDT", "POS",
    "PRP", "PRP$", "RP", "TO", "WDT", "WP", "WP$", "WRB",
})

_WEAK_WORDS = frozenset({'so', 'too', 'very', 'quite', 'rather', 'just'})

_AUXILIARIES = frozenset({
    'be', 'is', 'am', 'are', 'was', 'were', 'been', 'being',
    'have', 'has', 'had', 'having',
    'do', 'does', 'did',
    'will', 'would', 'shall', 'should',
    'can', 'could', 'may', 'might', 'must',
    'hath', 'doth', 'wilt', 'shalt', 'canst',
    'wouldst', 'shouldst', 'dost',
})

_DO_SUPPORT = frozenset({'do', 'does', 'did', 'doth', 'dost'})
_HAVE_AUX   = frozenset({'have', 'has', 'had', 'having', 'hath', 'hadst'})

_NLTK_PACKAGES = [
    ("tokenizers/punkt", "punkt_tab"),
    ("corpora/words", "words"),
    ("taggers/averaged_perceptron_tagger", "averaged_perceptron_tagger"),
    ("taggers/averaged_perceptron_tagger_eng", "averaged_perceptron_tagger_eng"),
]


def _inject_bundled_nltk_data():
    """Add the package's bundled corpora directory to NLTK's search path."""
    from importlib.resources import files
    try:
        data_dir = str(files('poetit').joinpath('data'))
    except Exception:
        data_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data')
    if data_dir not in nltk.data.path:
        nltk.data.path.insert(0, data_dir)


def _ensure_nltk_data():
    _inject_bundled_nltk_data()
    for path, name in _NLTK_PACKAGES:
        try:
            nltk.data.find(path)
        except LookupError:
            try:
                nltk.download(name, quiet=True)
            except Exception:
                pass


def _read_data(filename):
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


def _load_cmudict():
    text = _read_data('cmudict.dict')
    if not text:
        return {}
    result = {}
    for line in text.splitlines():
        if line.startswith(';;;') or not line.strip():
            continue
        parts = line.split()
        if len(parts) < 3:
            continue
        word = parts[0].lower()
        phonemes = parts[2:]   # parts[1] is the variant number
        result.setdefault(word, []).append(phonemes)
    return result


def word_at_cursor(text, idx):
    idx = max(0, min(idx, len(text)))
    start = idx
    while start > 0 and text[start - 1].isalpha():
        start -= 1
    end = idx
    while end < len(text) and text[end].isalpha():
        end += 1
    if start < end:
        return text[start:end], start, end
    end = idx
    while end > 0 and not text[end - 1].isalpha():
        end -= 1
    start = end
    while start > 0 and text[start - 1].isalpha():
        start -= 1
    return text[start:end], start, end


class Linguistics:
    def __init__(self):
        _ensure_nltk_data()
        self._cmu        = _load_cmudict()
        self._syl_tok    = SyllableTokenizer()
        self._rhyme_dict = self._load_rhyme_dict()
        self._thesaurus         = None
        self._thesaurus_loading = False
        self._spacy_nlp         = None
        self._spacy_loading     = False

    def start_background_loads(self):
        if SPACY_AVAILABLE:
            threading.Thread(target=self._load_spacy_background, daemon=True).start()
        threading.Thread(target=self._load_thesaurus_background, daemon=True).start()

    # ------------------------------------------------------------------ #
    # Syllable counting
    # ------------------------------------------------------------------ #

    def _best_cmu_entry(self, word):
        entries = self._cmu.get(word.lower())
        if not entries:
            return None
        if len(entries) == 1:
            return entries[0]
        counts = [sum(1 for ph in e if ph[-1].isdigit()) for e in entries]
        if len(set(counts)) == 1:
            return entries[0]
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

    def line_syllables(self, text):
        total = 0
        for token in word_tokenize(text):
            if not any(ch.isalpha() for ch in token):
                continue
            n = self._cmu_syllables(token)
            if n is None:
                n = self._fallback_syllables(token)
            total += n
        return total

    # ------------------------------------------------------------------ #
    # Rhyme dictionary and scheme
    # ------------------------------------------------------------------ #

    def _load_rhyme_dict(self):
        content = _read_data('rdict.js')
        if not content:
            return {}
        start = content.index('var rhdict = ') + len('var rhdict = ')
        end   = content.index('\nvar spdict = ')
        return json.loads(content[start:end].rstrip(';\n '))

    def _rhyme_suffix(self, word):
        entry = self._best_cmu_entry(word)
        if not entry:
            return None
        for i in range(len(entry) - 1, -1, -1):
            if entry[i][-1].isdigit():
                return tuple(re.sub(r'\d', '', ph) for ph in entry[i:])
        return None

    def get_rhymes(self, word):
        if not self._rhyme_dict:
            return []
        entries = self._cmu.get(word.lower())
        if not entries:
            return []
        phonemes = [re.sub(r'\d', '', ph) for ph in entries[0]]
        rev = list(reversed(phonemes))
        key = rev[0]
        if key not in self._rhyme_dict:
            return []
        results = []
        for s in range(len(rev) - 1, 0, -1):
            st  = ' '.join(rev[:s + 1])
            stl = len(st)
            for entry in self._rhyme_dict[key]:
                if entry[:stl] == st:
                    results.append(entry.split()[-1])
        seen, unique = set(), []
        for w in results:
            if w not in seen and w.lower() != word.lower():
                seen.add(w)
                unique.append(w)
        return unique

    def compute_rhyme_scheme(self, texts):
        scheme, anchors, next_idx = [], [], 0
        for text in texts:
            words_in = re.findall(r'[A-Za-z]+', text)
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
                letter = chr(ord('A') + next_idx) if next_idx < 26 else chr(ord('a') + next_idx - 26)
                next_idx += 1
                if suffix:
                    anchors.append((suffix, letter))
            scheme.append(letter)
        return scheme

    # ------------------------------------------------------------------ #
    # Thesaurus
    # ------------------------------------------------------------------ #

    def _load_thesaurus_background(self):
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
        raw = _read_data('th_en_US_new.js')
        if not raw:
            return {}
        raw = raw.strip()
        if raw.startswith('module.exports = '):
            raw = raw[len('module.exports = '):]
        if raw.endswith(';'):
            raw = raw[:-1]
        return json.loads(raw)

    def get_thesaurus(self, word):
        if self._thesaurus is None and not self._thesaurus_loading:
            self._thesaurus = self._load_thesaurus()
        key  = word.lower()
        syns = (self._thesaurus or {}).get(key, [])
        seen, result = {key}, []
        for s in syns:
            sl = s.lower()
            if sl not in seen:
                seen.add(sl)
                result.append(s)
        return result

    # ------------------------------------------------------------------ #
    # spaCy
    # ------------------------------------------------------------------ #

    def _load_spacy_background(self):
        if not SPACY_AVAILABLE or self._spacy_nlp is not None or self._spacy_loading:
            return
        self._spacy_loading = True
        try:
            self._spacy_nlp = _spacy.load("en_core_web_md")
        except Exception:
            pass
        finally:
            self._spacy_loading = False

    def get_spacy_doc(self, text):
        if not SPACY_AVAILABLE:
            return None
        if self._spacy_nlp is None:
            if self._spacy_loading:
                return None
            try:
                self._spacy_nlp = _spacy.load("en_core_web_md")
            except Exception:
                return None
        return self._spacy_nlp(text)

    # ------------------------------------------------------------------ #
    # Meter analysis
    # ------------------------------------------------------------------ #

    def _is_function(self, word, pos_tag, prev_word=None, dep=None):
        if dep is not None:
            if dep == 'ROOT':
                return False
            if dep in _WEAK_DEPS:
                return True
        if pos_tag in _FUNCTION_POS:
            return True
        if word.lower() in _WEAK_WORDS:
            return True
        if word.lower() in _AUXILIARIES:
            return True
        if (pos_tag in ('VBN', 'VBD') and prev_word
                and prev_word.lower() in _HAVE_AUX):
            return True
        return False

    def _syllabify_word(self, word, is_function=False):
        lower   = word.lower()
        entries = self._cmu.get(lower)

        if entries:
            best    = self._best_cmu_entry(lower)
            primary = [int(ph[-1]) for ph in best if ph[-1].isdigit()]
            if is_function and len(primary) == 1:
                stresses = None
                for entry in entries:
                    s = [int(ph[-1]) for ph in entry if ph[-1].isdigit()]
                    if s and max(s) == 0:
                        stresses = s
                        break
                if stresses is None:
                    stresses = [0]
            else:
                stresses = primary
        else:
            stresses = [0] * max(1, self._fallback_syllables(lower))

        n = max(1, len(stresses))
        wlen = len(word)
        base, rem = divmod(wlen, n)
        chunks, cursor = [], 0
        for k in range(n):
            size = base + (1 if k < rem else 0)
            chunks.append(word[cursor:cursor + size])
            cursor += size

        return [(chunks[k], stresses[k] if k < len(stresses) else 0) for k in range(n)]

    def _tag_line(self, text):
        word_tokens = re.findall(r'[A-Za-z]+', text)
        if not word_tokens:
            return []
        doc = self.get_spacy_doc(text)
        if doc is not None:
            result = [(tok.text, tok.tag_, tok.dep_) for tok in doc if tok.is_alpha]
            if result:
                return result
        try:
            tagged = nltk.pos_tag(word_tokens)
        except Exception:
            tagged = [(w, "NN") for w in word_tokens]
        return [(w, tag, '') for w, tag in tagged]

    def _compose_meter_line_nltk(self, text):
        tagged   = self._tag_line(text)
        tag_iter = iter(tagged)
        parts, prev_word = [], None
        for token in re.split(r'([A-Za-z]+)', text):
            if not token:
                continue
            if re.match(r'[A-Za-z]+$', token):
                _, pos_tag, dep = next(tag_iter, (token, "NN", ""))
                func_flag = self._is_function(token, pos_tag, prev_word, dep or None)
                sylls     = self._syllabify_word(token, func_flag)
                rendered  = []
                for stext, stress in sylls:
                    if stress == 1:   rendered.append(stext.upper())
                    elif stress == 2: rendered.append(stext.capitalize())
                    else:             rendered.append(stext.lower())
                parts.append(SEP_DOT.join(rendered))
                prev_word = token
            else:
                parts.append(token)
        return "".join(parts)

    def _compose_meter_line_prosodic(self, text):
        if not _PROSODIC_AVAILABLE or not text.strip():
            return None
        try:
            t = _prosodic.Text(text)
            t.parse()
            if not t.lines:
                return None
            line = t.lines[0]
            bp   = line.best_parse
            if bp is None:
                return None
            slots    = [s for s in bp.slots if s.syll is not None]
            slot_idx = 0
            parts    = []
            for wt in line.get_list('WordToken'):
                word_txt  = wt.txt
                word_core = word_txt.strip()
                leading   = word_txt[: len(word_txt) - len(word_core)]
                if leading:
                    parts.append(leading)
                if not word_core or not any(c.isalpha() for c in word_core):
                    parts.append(word_core)
                    continue
                target_len  = len(re.sub(r"[^a-z']+", '', word_core.lower()))
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
        except Exception:
            return None

    def compose_meter_line(self, text):
        result = self._compose_meter_line_prosodic(text)
        if result is not None:
            return result
        return self._compose_meter_line_nltk(text)
