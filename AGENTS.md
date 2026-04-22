# AGENTS.md

This file provides guidance to Qoder (qoder.com) when working with code in this repository.

## Running the Application

```bash
python main.py
```

Or run the package:

```bash
python -m poedit
```

After an editable install (`pip install -e .`), the `poedit` console entry point is also available.

## Setup

Install dependencies:

```bash
pip install -e .
```

The spaCy English model is required separately for dependency diagrams and improved POS tagging:

```bash
python -m spacy download en_core_web_md
```

NLTK data (cmudict, wordnet, punkt, POS taggers) is auto-downloaded on first launch.

## Architecture

This is a Python `tkinter` GUI application for editing poetry, with meter analysis, rhyme lookup, thesaurus, and dependency diagrams.

**Dual source files:** The codebase maintains two nearly identical copies of the application logic:
- `main.py` — standalone/legacy version, loads external data files via direct filesystem paths
- `poedit/app.py` — packaged version, loads bundled data via `importlib.resources` through `_read_data()`

When making changes, update both files to keep them in sync.

**UI structure:** The editor uses a scrollable canvas containing a grid of `tk.Entry` widgets — one row per poem line. Each row has three columns:
1. Text entry (the poem line)
2. Syllable-count margin
3. Rhyme-scheme letter

There is no single `tk.Text` widget; the document is the concatenation of all row entries.

**File format:** Poems are saved as plain `.txt` files with a sidecar `.txt.meta` JSON file storing font, size, and per-line character-run metadata.

**Optional dependencies gracefully degrade:**
- `prosodic` — preferred meter analysis backend
- `spacy` + `en_core_web_md` — dependency diagrams and better function-word detection
- `cairosvg` + `Pillow` — rendering dependency diagrams as PNG
- Thesaurus data (`th_en_US_new.js`) — synonym lookup

**Meter display:** Stress is shown by letter case in the meter row: UPPERCASE = primary stress, Capitalized = secondary stress, lowercase = unstressed.

**Data files:** `poedit/data/` contains symlinks to `rdict.js` (rhyme dictionary) and `th_en_US_new.js` (thesaurus). The package version resolves these via `importlib.resources`; the standalone version falls back to `../rhyming-dictionary/rdict.js` and `../node_modules/thesaurus/lib/th_en_US_new.js`.

## Build

```bash
pip install -e .
python -m build       # requires build in [project.optional-dependencies]
```

## Diagnostics

`probe.py` is a standalone CLI utility for inspecting NLTK/cmudict output for a given line:

```bash
python probe.py "Because I could not stop for Death"
```

## Tests

There is no test suite. `test5.py` and `test9.py` are ad-hoc WordNet exploration scripts, not tests.
