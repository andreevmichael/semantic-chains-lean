import SemanticChains.LemmaOne
import SemanticChains.MainTheorem
import SemanticChains.Section01.QuestionAndRoot
import SemanticChains.Section02.ContractGraph
import SemanticChains.Section02.QuestionInGraph
import SemanticChains.Section02.AnswerGraph
import SemanticChains.Section03.ContractSearch
import SemanticChains.Section03.InitialFacts
import SemanticChains.Section03.Ascent
import SemanticChains.Section03.Growth
import SemanticChains.Section04.Normalization
import SemanticChains.Section04.ChainExistence
import SemanticChains.Section04.LinkExpansion
import SemanticChains.Section04.OrderEnumeration
import SemanticChains.Section05.Registry
import SemanticChains.Section05.Representation
import SemanticChains.Section05.BinaryReadings
import SemanticChains.Section05.RegistryExamples
import SemanticChains.Section06.Rewording
import SemanticChains.Section06.ChainTransfer
import SemanticChains.Section06.RepeatedPresentations
import SemanticChains.Section06.AlternativeBases

/-! Формализация статьи Semantic Chains: From Reachable Facts to Justified Answers.
The README maps the sections of the paper to their Lean modules.

Порядок по актуальному черновику:
* Лемма 1. Из К1.1 и К3 выводится общий объект. К4 относится к восстановленному
  содержанию. В (*) обоснование выведенных фактов прослеживается до исходных.
* Основная теорема записана как MainTheorem : Prop. Доказательство: Section04.main_theorem.
  В условиях даны основание r, обосновывающее полный ответ, и носитель общего
  обозначения в выбранном раскрытии r.
* §1.1. Проверка возможного основания и достаточности предъявления подфактами: Section01.QuestionAndRoot.
* §2.1. Граф контракта и свидетельства его строгих рёбер: Section02.ContractGraph.
* §2.2. Указания на факт и объект, роль участника и открытое требование: Section02.QuestionInGraph.
* §2.3. Γ_S: конечность, достижимость, единственная верхняя вершина; D_S(r) и D_K(r): Section02.AnswerGraph.
* §3.1. Запросы по объекту, родителям и подфактам во всём контракте: Section03.ContractSearch.
* §3.2. Непустое конечное множество начальных фактов вопроса: Section03.InitialFacts.
* §3.3. Полнота подъёма, обнаружение основания r и остановка: Section03.Ascent.
* §3.4. Полнота двустороннего обхода, остановка и включение S ⊆ W: Section03.Growth.
* §4.1. Сохранение обоснования, S′ = Top(S) и S′ = {r}: Section04.Normalization.
* §4.2. Перенос обозначения, минимальное предъявление и однозвенная цепочка:
  Section04.SingleLink и Section04.ChainExistence.
* §4.3. Раскрытие звена, проверка нового порядка и сохранение обоснования: Section04.LinkExpansion.
* §4.4. Полнота и число порядков, совместная проверка и минимизация текстов:
  Section04.OrderEnumeration.
* §5.1. Записи реестра, канонизация содержания и ацикличность строгих рёбер: Section05.Registry.
* §5.2. Локальное и совместное раскрытие, обозначения и реализация П1–П2: Section05.Representation.
* Полные чтения бинарного родителя и проверка П3: Section05.BinaryReadings.
* §5.3. Оба примера реестра, порядок раскрытий и границы вывода: Section05.RegistryExamples.
* §6.1. Лексическое переоформление, нормализация и условия переноса W: Section06.Rewording.
* §6.2. Перенос обоснования, ключей и вклада при замене текстов: Section06.ChainTransfer.
* §6.3. Объединение повторных предъявлений и восстановление вхождений: Section06.RepeatedPresentations.
* §6.4. Независимая проверка разборов одного ответа, три конфигурации и пример Дэвида: Section06.AlternativeBases.
  Операции поиска и преобразования динамического ответа — в фиксированном Tₜ.

-/
