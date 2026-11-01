import siteConfig from '@generated/docusaurus.config';

export default function prismIncludeLanguages(PrismObject) {
  const {
    themeConfig: {prism},
  } = siteConfig;
  const {additionalLanguages} = prism;

  globalThis.Prism = PrismObject;
  additionalLanguages.forEach((lang) => {
    require(`prismjs/components/prism-${lang}`);
  });
  delete globalThis.Prism;

  PrismObject.languages.lean = {
    comment: [
      {pattern: /\/-[\s\S]*?-\//, greedy: true},
      {pattern: /--.*/, greedy: true},
    ],
    string: {pattern: /"(?:\\.|[^"\\])*"/, greedy: true},
    keyword:
      /\b(?:def|theorem|lemma|example|structure|class|instance|inductive|namespace|end|section|variable|open|import|where|by|fun|match|with|if|then|else|let|have|show|from|at|in|do|for|return|abbrev|private|protected|noncomputable|deriving|universe|set_option|mutual|termination_by|decreasing_by|simp|rw|exact|intro|intros|induction|cases|rcases|obtain|omega|grind|decide|unfold|apply|refine|calc|sorry|generalize|exfalso|by_cases|rfl|split)\b/,
    builtin: /\b(?:Nat|Int|Rat|Float|Bool|Fin|Array|List|Option|String|Prop|Type|Sort|IO|Unit)\b/,
    number: /\b\d+(?:\.\d+)?\b/,
    operator: /[←→↔∀∃λ¬∧∨≤≥≠≈∈×⟨⟩·∘↦⊢∑∏]|:=|=>|->|<-|\|>|<\||[+\-*\/=<>^|&]/,
    punctuation: /[()[\]{},.:;@#]/,
  };
}
