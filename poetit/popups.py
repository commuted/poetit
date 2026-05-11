import tkinter as tk
import tkinter.font as tkfont
from nltk.corpus import wordnet as wn

try:
    import resvg_py as _resvg
    from PIL import Image as _PILImage, ImageTk as _PILImageTk
    import io as _io
    DIAGRAM_AVAILABLE = True
except ImportError:
    DIAGRAM_AVAILABLE = False

_POS_LABEL = {'n': 'Noun', 'v': 'Verb', 'a': 'Adjective', 's': 'Adjective', 'r': 'Adverb'}


def show_word_list_popup(root, title, header, words, on_select, width=220, height=320):
    popup = tk.Toplevel(root)
    popup.title(title)
    popup.transient(root)
    popup.resizable(False, True)

    tk.Label(popup, text=header, anchor='w').pack(fill=tk.X, padx=6, pady=(6, 2))

    if not words:
        tk.Label(popup, text='None found.', fg='gray').pack(padx=6, pady=6)
        tk.Button(popup, text='Close', command=popup.destroy).pack(pady=6)
        return

    outer = tk.Frame(popup)
    outer.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)

    cv = tk.Canvas(outer, width=width, height=height, bg='white')
    sb = tk.Scrollbar(outer, orient='vertical', command=cv.yview)
    cv.configure(yscrollcommand=sb.set)
    cv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
    sb.pack(side=tk.RIGHT, fill=tk.Y)

    inner = tk.Frame(cv, bg='white')
    cv.create_window((0, 0), window=inner, anchor='nw')

    for word in words:
        def _cmd(w=word):
            on_select(w)
            popup.destroy()
        tk.Button(
            inner, text=word, anchor='w', relief='flat',
            bg='white', activebackground='#ddeeff', command=_cmd,
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


def show_definition_popup(root, word):
    synsets = wn.synsets(word)
    popup = tk.Toplevel(root)
    popup.title(f'Definition: "{word}"')
    popup.transient(root)
    popup.resizable(True, True)

    outer = tk.Frame(popup)
    outer.pack(fill=tk.BOTH, expand=True)

    cv = tk.Canvas(outer, width=380, height=440, bg='white', highlightthickness=0)
    sb = tk.Scrollbar(outer, orient='vertical', command=cv.yview)
    cv.configure(yscrollcommand=sb.set)
    cv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
    sb.pack(side=tk.RIGHT, fill=tk.Y)

    inner = tk.Frame(cv, bg='white', padx=10, pady=6)
    cv_win = cv.create_window((0, 0), window=inner, anchor='nw')

    cv.bind('<Configure>', lambda e: cv.itemconfig(cv_win, width=e.width))

    def _scroll(event):
        if event.num == 4:   cv.yview_scroll(-1, 'units')
        elif event.num == 5: cv.yview_scroll(1, 'units')
        else:                cv.yview_scroll(int(-1 * (event.delta / 120)), 'units')
    for seq in ('<MouseWheel>', '<Button-4>', '<Button-5>'):
        cv.bind(seq, _scroll)
        inner.bind(seq, _scroll)

    f_word = tkfont.Font(family='Helvetica', size=13, weight='bold')
    f_pos  = tkfont.Font(family='Helvetica', size=10, weight='bold', slant='italic')
    f_def  = tkfont.Font(family='Helvetica', size=10)
    f_sub  = tkfont.Font(family='Helvetica', size=9)

    tk.Label(inner, text=word.lower(), font=f_word, bg='white',
             anchor='w').pack(fill=tk.X, pady=(0, 6))

    if not synsets:
        tk.Label(inner, text='No definitions found.', font=f_def,
                 fg='gray', bg='white', anchor='w').pack(fill=tk.X)
    else:
        by_pos = {}
        for s in synsets:
            by_pos.setdefault(s.pos(), []).append(s)
        for pos in [p for p in ('n', 'v', 'a', 's', 'r') if p in by_pos]:
            tk.Label(inner, text=_POS_LABEL.get(pos, pos), font=f_pos,
                     fg='#555', bg='white', anchor='w').pack(fill=tk.X, pady=(8, 2))
            for idx, s in enumerate(by_pos[pos], 1):
                tk.Label(inner, text=f'{idx}.  {s.definition()}', font=f_def,
                         bg='white', anchor='w', justify='left',
                         wraplength=340).pack(fill=tk.X, padx=(8, 0))
                lemmas = [n.replace('_', ' ') for n in s.lemma_names()
                          if n.lower() != word.lower()]
                if lemmas:
                    tk.Label(inner, text='syn: ' + ',  '.join(lemmas), font=f_sub,
                             fg='#336', bg='white', anchor='w', justify='left',
                             wraplength=340).pack(fill=tk.X, padx=(20, 0))
                for ex in s.examples():
                    tk.Label(inner, text=f'"{ex}"', font=f_sub, fg='#555',
                             bg='white', anchor='w', justify='left',
                             wraplength=340).pack(fill=tk.X, padx=(20, 0))
                tk.Frame(inner, height=4, bg='white').pack()

    inner.update_idletasks()
    cv.configure(scrollregion=cv.bbox('all'))
    tk.Button(popup, text='Close', command=popup.destroy).pack(pady=6)


def _svg_escape(text):
    return (text.replace('&', '&amp;').replace('<', '&lt;')
                .replace('>', '&gt;').replace('"', '&quot;'))


def _arc_levels(words):
    """Assign each dependent word a nesting level (1-based) via interval graph coloring."""
    spans = [
        (min(w.id, w.head), max(w.id, w.head), w.id)
        for w in words if w.head > 0
    ]
    spans.sort(key=lambda s: (s[1] - s[0], s[0]))
    levels, buckets = {}, []
    for lo, hi, wid in spans:
        placed = False
        for lvl_idx, bucket in enumerate(buckets):
            if not any(lo < bhi and hi > blo for blo, bhi in bucket):
                bucket.append((lo, hi))
                levels[wid] = lvl_idx + 1
                placed = True
                break
        if not placed:
            buckets.append([(lo, hi)])
            levels[wid] = len(buckets)
    return levels


def _stanza_to_svg(doc, bg="#fffef0", color="#003388"):
    """Render a Stanza doc's first sentence as a dependency arc diagram SVG."""
    if not doc or not doc.sentences:
        return (f'<svg xmlns="http://www.w3.org/2000/svg" width="300" height="60"'
                f' style="background:{bg}"><text x="10" y="35"'
                f' font-family="sans-serif" font-size="13" fill="#555">'
                f'No parse available.</text></svg>')

    words = doc.sentences[0].words
    n = len(words)

    col_w        = 110   # horizontal pixels per word
    pad_x        = 60    # left/right margin
    entry_offset = 22    # gap between word baseline and arc attachment point
    level_step   = 34    # px per nesting level
    pad_top      = 28    # clearance above topmost arc label
    root_clear   = 42    # space needed for the ROOT indicator above entry_y

    arc_lvls  = _arc_levels(words)
    max_level = max(arc_lvls.values(), default=1)

    entry_y  = pad_top + max(max_level * level_step + 14, root_clear)
    baseline = entry_y + entry_offset
    total_h  = baseline + 48
    total_w  = pad_x * 2 + max(n - 1, 0) * col_w

    arcs, arc_labels, word_els = [], [], []

    marker = (
        f'<defs><marker id="arr" markerWidth="7" markerHeight="7"'
        f' refX="6" refY="3.5" orient="auto" markerUnits="userSpaceOnUse">'
        f'<path d="M 0 0 L 7 3.5 L 0 7 Z" fill="{color}"/>'
        f'</marker></defs>'
    )

    for word in words:
        xi = pad_x + (word.id - 1) * col_w

        word_els.append(
            f'<text x="{xi}" y="{baseline}" text-anchor="middle"'
            f' font-family="Helvetica,Arial,sans-serif" font-size="13"'
            f' font-weight="bold" fill="#111">{_svg_escape(word.text)}</text>'
        )
        pos = word.xpos or word.upos or ''
        word_els.append(
            f'<text x="{xi}" y="{baseline + 18}" text-anchor="middle"'
            f' font-family="Helvetica,Arial,sans-serif" font-size="10"'
            f' fill="#666">{_svg_escape(pos)}</text>'
        )

        if word.head == 0:
            root_y0 = entry_y - 30
            arcs.append(
                f'<line x1="{xi}" y1="{root_y0}" x2="{xi}" y2="{entry_y}"'
                f' stroke="{color}" stroke-width="1.5" marker-end="url(#arr)"/>'
            )
            arc_labels.append(
                f'<text x="{xi}" y="{root_y0 - 5}" text-anchor="middle"'
                f' font-family="Helvetica,Arial,sans-serif" font-size="10"'
                f' fill="{color}">root</text>'
            )
        else:
            xh     = pad_x + (word.head - 1) * col_w
            level  = arc_lvls.get(word.id, 1)
            peak_y = entry_y - level * level_step
            mid_x  = (xi + xh) / 2

            # Cubic bezier: control points directly above endpoints → vertical rise,
            # flat top, vertical drop; eliminates diagonal crossings between arcs
            arcs.append(
                f'<path d="M {xh} {entry_y} C {xh} {peak_y}, {xi} {peak_y}, {xi} {entry_y}"'
                f' stroke="{color}" fill="none" stroke-width="1.5"'
                f' marker-end="url(#arr)"/>'
            )

            # Cubic bezier at t=0.5: y = 0.25·entry_y + 0.75·peak_y (actual curve position)
            lbl_center_y = round(entry_y * 0.25 + peak_y * 0.75)
            lbl_text = word.deprel or ""
            lbl_w = len(lbl_text) * 6 + 6
            arc_labels.append(
                f'<rect x="{round(mid_x - lbl_w / 2)}" y="{lbl_center_y - 6}"'
                f' width="{lbl_w}" height="11" fill="{bg}"/>'
            )
            arc_labels.append(
                f'<text x="{mid_x}" y="{lbl_center_y + 4}" text-anchor="middle"'
                f' font-family="Helvetica,Arial,sans-serif" font-size="10"'
                f' fill="{color}">{_svg_escape(lbl_text)}</text>'
            )

    return (
        f'<svg xmlns="http://www.w3.org/2000/svg"'
        f' width="{total_w}" height="{total_h}" style="background:{bg}">\n'
        + marker + '\n'
        + '\n'.join(arcs) + '\n'
        + '\n'.join(arc_labels) + '\n'
        + '\n'.join(word_els) + '\n'
        + '</svg>'
    )


def show_diagram_popup(root, text, doc, screen_w, screen_h):
    svg = _stanza_to_svg(doc)
    png_bytes = _resvg.svg_to_bytes(svg_string=svg)
    img = _PILImage.open(_io.BytesIO(png_bytes))

    popup = tk.Toplevel(root)
    popup.title("Dependency Diagram")
    popup.transient(root)
    popup.resizable(True, True)

    tk.Label(popup, text=text, font=("Helvetica", 11), wraplength=700,
             justify="left", pady=4).pack(fill=tk.X, padx=8)

    # Word annotation row: text / deprel / upos
    info_frame = tk.Frame(popup, bg="#eef2fb")
    info_frame.pack(fill=tk.X, padx=8, pady=(0, 4))
    if doc and doc.sentences:
        for word in doc.sentences[0].words:
            if word.text.isalpha():
                cell = tk.Frame(info_frame, bg="#eef2fb", padx=4)
                cell.pack(side="left")
                tk.Label(cell, text=word.text,   font=("Courier", 9, "bold"), bg="#eef2fb").pack()
                tk.Label(cell, text=word.deprel, font=("Courier", 8), fg="#005500", bg="#eef2fb").pack()
                tk.Label(cell, text=word.upos,   font=("Courier", 8), fg="#550000", bg="#eef2fb").pack()

    frame = tk.Frame(popup)
    frame.pack(fill=tk.BOTH, expand=True)

    h_sb = tk.Scrollbar(frame, orient="horizontal")
    v_sb = tk.Scrollbar(frame, orient="vertical")
    cv   = tk.Canvas(frame, bg="white", xscrollcommand=h_sb.set, yscrollcommand=v_sb.set)
    h_sb.configure(command=cv.xview)
    v_sb.configure(command=cv.yview)
    h_sb.pack(side=tk.BOTTOM, fill=tk.X)
    v_sb.pack(side=tk.RIGHT,  fill=tk.Y)
    cv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

    photo = _PILImageTk.PhotoImage(img)
    cv.create_image(4, 4, anchor="nw", image=photo)
    cv._img_ref = photo
    cv.configure(scrollregion=(0, 0, img.width + 8, img.height + 8))

    for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
        cv.bind(seq, lambda e, s=cv: (
            s.yview_scroll(-1, "units") if e.num == 4
            else s.yview_scroll(1, "units") if e.num == 5
            else s.xview_scroll(int(-1 * (e.delta / 120)), "units")
        ))

    w = min(img.width + 30, screen_w - 100)
    h = min(img.height + 140, screen_h - 100)
    popup.geometry(f"{w}x{h}")
    tk.Button(popup, text="Close", command=popup.destroy).pack(pady=6)
