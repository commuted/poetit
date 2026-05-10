import tkinter as tk
import tkinter.font as tkfont
from nltk.corpus import wordnet as wn

try:
    import resvg_py as _resvg
    from PIL import Image as _PILImage, ImageTk as _PILImageTk
    import io as _io
    from spacy import displacy as _displacy
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


def show_diagram_popup(root, text, doc, screen_w, screen_h):
    options = {"compact": False, "bg": "#fffef0", "color": "#003388", "fine_grained": True}
    svg = _displacy.render(doc, style="dep", options=options)
    png_bytes = _resvg.svg_to_bytes(svg_string=svg)
    img = _PILImage.open(_io.BytesIO(png_bytes))

    popup = tk.Toplevel(root)
    popup.title("Dependency Diagram")
    popup.transient(root)
    popup.resizable(True, True)

    tk.Label(popup, text=text, font=("Helvetica", 11), wraplength=700,
             justify="left", pady=4).pack(fill=tk.X, padx=8)

    info_frame = tk.Frame(popup, bg="#eef2fb")
    info_frame.pack(fill=tk.X, padx=8, pady=(0, 4))
    for tok in doc:
        if tok.is_alpha:
            cell = tk.Frame(info_frame, bg="#eef2fb", padx=4)
            cell.pack(side="left")
            tk.Label(cell, text=tok.text, font=("Courier", 9, "bold"), bg="#eef2fb").pack()
            tk.Label(cell, text=tok.dep_,  font=("Courier", 8), fg="#005500", bg="#eef2fb").pack()
            tk.Label(cell, text=tok.pos_,  font=("Courier", 8), fg="#550000", bg="#eef2fb").pack()
            if tok.ent_type_:
                tk.Label(cell, text=f"[{tok.ent_type_}]", font=("Courier", 7),
                         fg="#884400", bg="#eef2fb").pack()

    frame = tk.Frame(popup)
    frame.pack(fill=tk.BOTH, expand=True)

    h_sb = tk.Scrollbar(frame, orient="horizontal")
    v_sb = tk.Scrollbar(frame, orient="vertical")
    cv   = tk.Canvas(frame, bg="white", xscrollcommand=h_sb.set, yscrollcommand=v_sb.set)
    h_sb.configure(command=cv.xview)
    v_sb.configure(command=cv.yview)
    h_sb.pack(side=tk.BOTTOM, fill=tk.X)
    v_sb.pack(side=tk.RIGHT, fill=tk.Y)
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
