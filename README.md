# Semantic Chains: From Reachable Facts to Justified Answers

Lean 4 formalization of the paper by **Misha Andreev** ([arXiv:2611.14252](https://arxiv.org/abs/2611.14252)).

[Theorem statement](SemanticChains/MainTheorem.lean#L168) · [Proof](SemanticChains/Section04/ChainExistence.lean#L94) · [Search, normalization and chain construction](SemanticChains/Section04/ChainExistence.lean#L67)

Which facts can a search reach from the objects mentioned in a question, and which of those facts justify its answer? The theorem starts with a sufficient root fact and a selected expansion containing a recorded designation of an object shared by the question and the full answer. It proves that search reaches the root and covers the selected expansion. Normalization leaves the root, for which there exists an admissible one-link text carrying the shared object at both ends of the chain.

[24 worked examples from LoCoMo, RHELM, and EverMemBench](examples/24-question-audit.md)

## Build

With [Elan](https://github.com/leanprover/elan) installed, run the following command in the repository root. The toolchain is pinned to Lean 4.24.0. The project has no external Lean package dependencies.

```sh
lake build
```

## Guide to the proof

| Paper | Given | Proved | Lean source |
| --- | --- | --- | --- |
| Lemma 1 | A question and its full answer under the model conditions | They share an object. In the dynamic case, justification can be traced through valid extensions to the original facts. | [LemmaOne](SemanticChains/LemmaOne.lean) |
| §§1–2 | A candidate root and its selected expansion in the contract | The selected graph has a unique top vertex. | [Question and root](SemanticChains/Section01/QuestionAndRoot.lean), [answer graph](SemanticChains/Section02/AnswerGraph.lean) |
| §3 | A recorded occurrence of a shared object in the selected expansion | Ascent finds the root, and bidirectional search covers the selected facts. | [Ascent](SemanticChains/Section03/Ascent.lean), [growth](SemanticChains/Section03/Growth.lean) |
| §§4.1–4.2 | A selected expansion with a sufficient root and a shared-object witness | Absorption preserves justification. The normalized expansion admits a one-link chain. | [Normalization](SemanticChains/Section04/Normalization.lean), [chain existence](SemanticChains/Section04/ChainExistence.lean) |
| §§4.3–4.4 | The underlying facts of candidate links | Enumeration covers the specified class of orders. Admissibility of a particular order requires compatible texts. | [Link expansion](SemanticChains/Section04/LinkExpansion.lean), [order enumeration](SemanticChains/Section04/OrderEnumeration.lean) |
| §5 | Fact records and interpreted occurrences in a positive registry | Local substitution preserves full content. The binary examples distinguish retaining both children from retaining their relation in the same roles. | [Representation](SemanticChains/Section05/Representation.lean), [binary readings](SemanticChains/Section05/BinaryReadings.lean) |
| §6 | Reworded texts, repeated occurrences or alternative justifications | The transfer criteria specify when a chain survives a change of presentation. Alternative justifications can be checked separately. | [Chain transfer](SemanticChains/Section06/ChainTransfer.lean), [repeated presentations](SemanticChains/Section06/RepeatedPresentations.lean), [alternative justifications](SemanticChains/Section06/AlternativeBases.lean) |

The [abstract interface for P2](SemanticChains/Presentation.lean#L12) requires expansion to yield a full parent representation and preserve the object designation carried by the child. In the [concrete registry](SemanticChains/Section05/Representation.lean), substitution fills a specified occurrence while its surrounding context stays fixed.
