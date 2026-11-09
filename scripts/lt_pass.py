"""LanguageTool pass over LEAIN4 mdx prose (FR + EN). Writes raw findings to JSON."""
import json, re, glob, time, urllib.request, urllib.parse, sys, os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WEB = os.path.join(ROOT, 'website')

def strip_prose(path):
    lines = []
    in_code = False
    for ln in open(path, encoding='utf-8'):
        if ln.strip().startswith('```'):
            in_code = not in_code
            continue
        if in_code:
            continue
        s = ln.strip()
        if s.startswith('import ') or s.startswith('open ') or re.match(r'^\s*(theorem|def|example|namespace|end)\b', ln):
            continue
        if s.startswith('<') and not s.startswith('<p'):  # mdx components
            continue
        if s.startswith('![') or s.startswith('import '):
            continue
        s = re.sub(r'`[^`]*`', 'CODE', s)           # inline code
        s = re.sub(r'\[([^\]]*)\]\([^)]*\)', r'\1', s)  # links -> text
        s = re.sub(r'^#+\s*', '', s)
        if len(re.sub(r'\W', '', s)) < 20:
            continue
        lines.append(s)
    return '\n'.join(lines)

def check(text, lang):
    out = []
    # chunk under 20k chars on line boundaries
    chunk = ''
    for para in text.split('\n'):
        if len(chunk) + len(para) > 18000:
            out.append(chunk); chunk = ''
        chunk += para + '\n'
    if chunk.strip():
        out.append(chunk)
    res = []
    for i, c in enumerate(out):
        data = urllib.parse.urlencode({'language': lang, 'text': c, 'enableRules': '', 'level': 'default'}).encode()
        req = urllib.request.Request('https://api.languagetool.org/v2/check', data=data)
        with urllib.request.urlopen(req, timeout=60) as r:
            j = json.load(r)
        base = len('\n'.join(out[:i]))
        for m in j.get('matches', []):
            ctx = m['context']['text']
            res.append({'rule': m['rule']['id'], 'severity': m.get('rule', {}).get('message', '')[:60],
                        'msg': m.get('message', '')[:120], 'context': ctx[:100],
                        'repl': [x['value'] for x in m.get('replacements', [])[:3]]})
        time.sleep(3.2)
    return res

def main():
    report = {}
    files = sorted(glob.glob(os.path.join(WEB, 'docs', '*.mdx')))
    files += sorted(glob.glob(os.path.join(WEB, 'i18n', 'fr', 'docusaurus-plugin-content-docs', 'current', '*.mdx')))
    only = sys.argv[1] if len(sys.argv) > 1 else None
    for f in files:
        name = os.path.relpath(f, WEB)
        if only and only not in name:
            continue
        fr = 'i18n' in f
        prose = strip_prose(f)
        if not prose.strip():
            continue
        print('checking', name, len(prose), flush=True)
        report[name] = check(prose, 'fr' if fr else 'en-US')
    out = os.path.join(ROOT, 'scripts', 'lt_report.json')
    json.dump(report, open(out, 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
    tot = sum(len(v) for v in report.values())
    print('MATCHES', tot, '->', out)

main()
