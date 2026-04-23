# Poedit

A desktop poetry editor with built-in meter analysis, rhyme lookup, thesaurus, dictionary, and dependency diagrams. Built with Python and tkinter.

## Install

```bash
pip install -e .
```

This pulls in all dependencies including the spaCy English model. NLTK data (cmudict, wordnet, punkt) is downloaded automatically on first launch.

## Run

```bash
poedit
```

Or:

```bash
python -m poedit
```

## Features

### Editing

Each line of the poem occupies its own row. Press **Enter** to create a new line and move down. Press **BackSpace** on an empty line at cursor position 0 to delete the line and move up. **Up/Down** arrows and **Tab** navigate between lines.

### Syllable counts

A grey margin column to the right of each line shows its syllable count, computed from CMU Pronouncing Dictionary entries with NLTK's SyllableTokenizer as a fallback.

### Rhyme scheme

A green column on the far right displays the rhyme scheme letter for each line. Rhyme detection uses phoneme-suffix equality from cmudict — two words are assigned the same letter when their phonemes from the last stressed vowel onward are identical.

### Meter

Click the **Meter** toolbar button to toggle a meter display above each line. Stress is shown by letter case:

- **UPPERCASE** — primary stress
- **Capitalized** — secondary stress
- **lowercase** — unstressed

Syllable boundaries are marked with a middle dot (·). Function words (determiners, auxiliaries, prepositions, etc.) are automatically detected and destressed. When the `prosodic` library is available, it is preferred for metrically-informed stress analysis; otherwise NLTK + cmudict with POS tagging is used.

### Rhyme

Click in a line to position the cursor on or after a word, then click **Rhyme** to see a popup of rhyming words. Click a rhyme to replace the word in your poem. You can also type a word directly into the lookup field that appears next to the Rhyme button and press Enter.

### Definition

Position the cursor on a word and click **Definition** to see its WordNet definitions grouped by part of speech, with synonyms and usage examples.

### Thesaurus

Position the cursor on a word and click **Thesaurus** to see a list of synonyms. Click a synonym to replace the word in your poem.

### Dependency diagram

Position the cursor on a line and click **Diagram** to render a spaCy dependency parse of that line. The diagram shows grammatical relationships between words, with POS and dependency labels in an annotation row above the tree.

### File operations

- **File → Open** — load a `.txt` file (UTF-8)
- **File → Save / Save As** — save the poem as `.txt` with a sidecar `.txt.meta` JSON file that stores font settings and per-line formatting metadata
- **File → New** — clear the editor (prompts to save if there are unsaved changes)

### Font

The **Font** and **Size** menus let you change the editor typeface. Font choice is persisted in the `.meta` file.
