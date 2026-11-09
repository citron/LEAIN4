# -*- coding: utf-8 -*-
"""FR content quality pass: accents (body+captions), NBSP typography, targeted commas."""
import re, glob

NBSP = '\u00A0'

G = {
 'theoreme': 'théorème', 'theoremes': 'théorèmes', 'decroissance': 'décroissance',
 'decroitre': 'décroître', 'decroit': 'décroît',
 'tracee': 'tracée', 'tracees': 'tracées', 'retrecie': 'rétrécie',
 'voluntairement': 'volontairement', 'predit': 'prédit', 'propriete': 'propriété',
 'etapes': 'étapes', 'demontre': 'démontré',
 'modele': 'modèle', 'modeles': 'modèles', 'meme': 'même', 'memes': 'mêmes',
 'entrainement': 'entraînement', 'entraine': 'entraîne', 'entrainee': 'entraînée',
 'entree': 'entrée', 'entrees': 'entrées', 'etat': 'état', 'etats': 'états',
 'apres': 'après', 'parametre': 'paramètre', 'parametres': 'paramètres',
 'phenomene': 'phénomène', 'theorique': 'théorique', 'theoriques': 'théoriques',
 'precision': 'précision', 'granularite': 'granularité', 'coeur': 'cœur',
 'critere': 'critère', 'criteres': 'critères', 'systeme': 'système',
 'systemes': 'systèmes', 'probleme': 'problème', 'problemes': 'problèmes',
 'element': 'élément', 'elements': 'éléments', 'calculee': 'calculée',
 'genere': 'génère', 'vallee': 'vallée', 'etroite': 'étroite',
 'echeancier': 'échéancier', 'detruit': 'détruit', 'precise': 'précise',
 'vise': 'visé',
}
gpat = re.compile(r'\b(' + '|'.join(G) + r')\b')

C = {
 'equation': 'équation', 'frontiere': 'frontière', 'derivee': 'dérivée',
 'sigmoide': 'sigmoïde', 'evanescence': 'évanescence', 'decouper': 'découper',
 'separe': 'sépare', 'separateur': 'séparateur', 'epaisse': 'épaisse',
 'achetent': 'achètent', 'unites': 'unités', 'cachees': 'cachées',
 'unite': 'unité', 'echelle': 'échelle', 'premiere': 'première',
 'difference': 'différence', 'differences': 'différences', 'dessinee': 'dessinée',
 'dessine': 'dessiné', 'pousse': 'poussé', 'negatif': 'négatif',
 'empilees': 'empilées', 'croitre': 'croître', 'receptif': 'réceptif',
 'coince': 'coincé', 'identite': 'identité', 'demontree': 'démontrée',
 'reseau': 'réseau', 'fenetre': 'fenêtre', 'carre': 'carré',
 'denrouler': 'Dérouler', 'retropropagation': 'rétropropagation',
 'lineairement': 'linéairement', 'arriere': 'arrière', 'tache': 'tâche',
 'memoire': 'mémoire', 'evanouit': 'évanouit', 'decide': 'décide',
 'reecrit': 'réécrit', 'reglable': 'réglable', 'cles': 'clés',
 'ecart': 'écart', 'demontres': 'démontrés', 'repartit': 'répartit',
 'egales': 'égales', 'moities': 'moitiés', 'pres': 'près',
 'donnees': 'données', 'execute': 'exécuté', 'achete': 'achète',
 'serree': 'serrée', 'distortion': 'distorsion', 'probabilite': 'probabilité',
 'generateur': 'générateur', 'reel': 'réel', 'recompense': 'récompense',
 'iteration': 'itération', 'geometriquement': 'géométriquement',
 'imagines': 'imaginées', 'penalite': 'pénalité', 'effondre': 'effondré',
 'regularisation': 'régularisation', 'penalise': 'pénalisé',
 'generalisation': 'généralisation', 'decomposition': 'décomposition',
 'capacite': 'capacité', 'similarite': 'similarité', 'negatifs': 'négatifs',
 'apparie': 'apparié', 'prouve': 'prouvé',
}
cpat = re.compile(r'\b(' + '|'.join(C) + r")\b")

PHRASES = [
 ("qu'utilise the théorème", "qu'utilise le théorème"),
 ("que the théorème", "que le théorème"),
]

CAP_PHRASES = [
 ("l'etat", "l'état"), ("d'un cote", "d'un côté"),
 ("a parts egales", "à parts égales"),
 ("la ou", "là où"), ("d'un bord a l'autre", "d'un bord à l'autre"),
 ("a pleine", "à pleine"), ("a t =", "à t ="),
 ("98 % a l'ecart", "98 % à l'écart"),
]

COMMAS = [
 ("ch04-autodiff.mdx",
  "s\u2019il est vrai pour les petits morceaux il l\u2019est pour le grand",
  "s\u2019il est vrai pour les petits morceaux, il l\u2019est pour le grand"),
 ("ch07-rnn.mdx",
  "Pour des vecteurs r\u00e9els nous utilisons des tableaux",
  "Pour des vecteurs r\u00e9els, nous utilisons des tableaux"),
 ("ch07-rnn.mdx",
  "cinq pas plus loin il vaut", "cinq pas plus loin, il vaut"),
 ("ch08-lstm.mdx",
  "honn\u00eatement que sur notre petite t\u00e2che il ne bat pas le RNN simple",
  "honn\u00eatement que sur notre petite t\u00e2che, il ne bat pas le RNN simple"),
 ("ch11-gan.mdx",
  "En g\u00e9n\u00e9ral il ne converge pas", "En g\u00e9n\u00e9ral, il ne converge pas"),
 ("ch12-diffusion.mdx",
  "Contrairement \u00e0 un GAN il n'y a pas de jeu",
  "Contrairement \u00e0 un GAN, il n'y a pas de jeu"),
 ("ch13-rl.mdx",
  "apr\u00e8s $k$ balayages elle vaut", "apr\u00e8s $k$ balayages, elle vaut"),
 ("ch15-jepa.mdx",
  "\u00e0 chaque pas elle se rapproche", "\u00e0 chaque pas, elle se rapproche"),
 ("ch16-tools.mdx",
  "\u00c0 chaque fois nous avons cit\u00e9 une propri\u00e9t\u00e9",
  "\u00c0 chaque fois, nous avons cit\u00e9 une propri\u00e9t\u00e9"),
]

n1 = n2 = nc = ntyp = 0
for f in glob.glob('website/i18n/fr/docusaurus-plugin-content-docs/current/*.mdx'):
    lines = open(f, encoding='utf-8').read().replace('\r\n', '\n').split('\n')
    fm_end = 0
    if lines[0].strip() == '---':
        fm_end = next(i for i in range(1, len(lines)) if lines[i].strip() == '---')
    out, in_code = list(lines[:fm_end + 1]), False
    for ln in lines[fm_end + 1:]:
        if ln.strip().startswith('```'):
            in_code = not in_code; out.append(ln); continue
        if in_code:
            out.append(ln); continue

        def cap(m):
            global n2
            s = m.group(2)
            for a, b in CAP_PHRASES:
                s = s.replace(a, b)
            for a, b in PHRASES:
                s = s.replace(a, b)
            s2 = cpat.sub(lambda mm: C[mm.group(1)], s)
            s2 = gpat.sub(lambda mm: G[mm.group(1)], s2)
            if s2 != s:
                n2 += 1
            return m.group(1) + s2 + '"'
        ln2 = re.sub(r'(caption="|alt=")([^"]*)"', cap, ln)

        s = ln2.strip()
        struct = (s.startswith('#') or s.startswith(':::') or s.startswith('<')
                  or s.startswith('![') or s.startswith('|'))
        has_math = '$' in ln2

        def fix(seg):
            if seg.startswith('`') or '$' in seg or 'http' in seg:
                return seg
            a = gpat.sub(lambda mm: G[mm.group(1)], seg)
            if struct or has_math:
                return a
            return re.sub(r'(?<=[^ \t\n;:])([;:!?])(?=[ \t"”»)]|$)', NBSP + r'\1', a)

        parts = re.split(r'(`[^`]*`|\$[^$]*\$|https?://\S+)', ln2)
        new = ''.join(p if (p.startswith('`') or p.startswith('$') or p.startswith('http'))
                      else fix(p) for p in parts)
        n1 += len(gpat.findall(ln2)) - len(gpat.findall(new))
        ntyp += new.count(NBSP) - ln2.count(NBSP)
        out.append(new)
    open(f, 'w', encoding='utf-8', newline='\n').write('\n'.join(out))

import os
for name, old, new in COMMAS:
    f = 'website/i18n/fr/docusaurus-plugin-content-docs/current/' + name
    t = open(f, encoding='utf-8').read()
    c = t.count(old)
    if c == 1:
        open(f, 'w', encoding='utf-8', newline='\n').write(t.replace(old, new))
        nc += 1
    else:
        print('COMMA_ISSUE', c, name)
print('accents body:', n1, 'captions:', n2, 'typo NBSP:', ntyp, 'commas:', nc)
