import re, glob, sys
# Scan FR+EN mdx for common quality defects. Skips code fences.
stats = {}
def add(k, f, line):
    stats.setdefault(k, []).append((f, line))
for f in sorted(glob.glob('docs/*.mdx') + glob.glob('i18n/fr/docusaurus-plugin-content-docs/current/*.mdx')):
    fr = 'i18n/fr' in f
    in_code = False
    for i, line in enumerate(open(f, encoding='utf-8'), 1):
        if line.strip().startswith('```'):
            in_code = not in_code; continue
        if in_code: continue
        if fr:
            # French typography: space required before ; ! ? (not in links/images URLs)
            for m in re.finditer(r'[^ \t\n][;!?]', line):
                seg = line[max(0,m.start()-60):m.end()+30]
                if '(' in seg.split(';')[0][-25:] and 'http' in seg: continue
                add('fr_punct_space', f, f'{i}: {line.strip()[:90]}')
            # straight apostrophe inside French words (typo inconsistency)
            if re.search(r"[a-zA-Z]'[aàeiouâéèêôûç](e|s|t|x|ai|es|ez|ent)\b", line) and 'http' not in line and 'file=' not in line:
                add('fr_straight_apostrophe', f, f'{i}: {line.strip()[:90]}')
        # doubled words
        m = re.search(r'\b(\w{3,})\s+\1\b', line, re.I)
        if m: add('doubled_word', f, f'{i}: {line.strip()[:90]}')
        # missing space after punctuation before a capital/word
        if re.search(r'[a-z]\)\.(?=[A-ZÀ-Ü])', line): add('missing_space_period', f, f'{i}: {line.strip()[:90]}')
        # double spaces mid-sentence (non-table)
        if re.search(r'\S  \S', line) and not line.strip().startswith('|'): add('double_space', f, f'{i}: {line.strip()[:90]}')
tot = 0
for k in sorted(stats):
    seen = stats[k]
    print(f'== {k}: {len(seen)}')
    for f, l in seen[:6]: print(f'   {f} L{l}')
    tot += len(seen)
print('TOTAL', tot)
