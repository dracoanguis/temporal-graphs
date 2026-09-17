# temporal-graphs

Bibliothèque Lean 4 + Mathlib sur les **graphes temporels** (arêtes étiquetées par un temps
`ℕ`). C'est un *rework* d'une bibliothèque précédente de l'auteur. L'objectif final n'est pas
figé au-delà de : prouver des résultats récents sur les graphes temporels — en particulier une
borne de spanner `O(n log n)` pour les cliques temporelles, via la technique de
*« dismountability »* de **Casteigts, Peters & Schoeters, *Temporal Cliques Admit Sparse
Spanners*, ICALP 2019 / JCSS**. Le scope peut s'élargir à d'autres résultats récents au fil du
travail.

Ce fichier est spécifique à ce projet. Le workflow Lean générique (lean-lsp, lean4-skills,
discipline anti-`sorry`, commits atomiques) est déjà couvert par le `CLAUDE.md` global — pas
besoin de le répéter ici.

## Convention de travail Claude Code (worktree, branches)

- Toute session doit s'isoler dans un **worktree** (`EnterWorktree`) avant de modifier des
  fichiers de ce dépôt.
- **`monde-apres` est la branche principale de développement** de ce projet, même si `main` est
  la branche par défaut au sens Git. **`main` est strictement interdite à toute modification** :
  jamais de commit, de push, ni de merge dessus.
- Piège pratique : `EnterWorktree` (baseRef `fresh` par défaut) crée le nouveau worktree à
  partir de `origin/main`, qui est en retard sur `monde-apres` (le travail récent n'y est pas
  encore fusionné). Juste après avoir créé le worktree, le mettre à jour avec
  `git merge --ff-only monde-apres` (sûr : `origin/main` est un ancêtre de `monde-apres`) avant
  de commencer à travailler.
- Une fois le travail validé, fusionner le(s) commit(s) du worktree dans `monde-apres`
  (fast-forward) et pousser `origin/monde-apres` — ne pas laisser une branche `worktree-<nom>`
  orpheline comme livrable final poussé sur le remote.

## Carte du dépôt

| Fichier | Rôle | Analogue Mathlib |
|---|---|---|
| `TemporalGraph/Init.lean` | Rule-set aesop `LooplessTemporalGraph` (nom hérité, voir Conventions) | `SimpleGraph/Init.lean` |
| `TemporalGraph/Basic.lean` | Type central `TemporalGraph V` (juste `Adj : V → V → ℕ → Prop`), prédicats `IsSymm`/`IsLoopless`/`IsSimple`/`IsClique`/`IsProper`/`IsHappy`, `EarliestEdge`/`LatestEdge`/`EarliestNeighbor`/`LatestNeighbor`, ordre `≤`/`⊥`, `Footprint` (→ `Digraph`), `NeighborhoodSet`, `EdgeSet`, `size` | `SimpleGraph`, mais sans `symm`/`loopless` bundlés |
| `TemporalGraph/NonemptyTemporalWalk.lean`, `TemporalGraph/TemporalWalk.lean` | Marches temporelles non strictes, à temps croissant | `SimpleGraph.Walk` |
| `TemporalGraph/SubTemporalGraph.lean` | Sous-graphe temporel (`Verts`+`Adj`+preuves), coercions, treillis borné, `induce`/`deleteVerts`/`addVerts`/`addEdge` | `SimpleGraph.Subgraph` |
| `TemporalGraph/Connectivity/Basic.lean`, `Connectivity/SubTemporalGraph.lean` | `Reachable`, `TemporallyConnected`, spanners (`IsSpanner`, `IsTCSpanner`) | `SimpleGraph.Connectivity` |
| `TemporalGraph/Dismountability/Basic.lean` | `Dismountable`, `TwoHopDismountable`, partition `Vminus`/`Vplus`/`Vzero`, bijections earliest/latest-neighbor — correspond au Théorème 2.1 et aux Lemmes 3.1–3.4 du papier | — |
| `TemporalGraph/Dismountability/Operations.lean` | Opérations `dismount`/`mount`/`twoHopMount` et leurs théorèmes de correction (`dismountability`, `twoHopDismountability`) | — |
| `TemporalGraph.lean` (racine) | Fichier de démo/scratch, largement commenté, **actuellement cassé** (voir ci-dessous) | — |

## État actuel : refactor en cours

Le commit `bcf2d41` (« Split LooplessTemporalGraph into TemporalGraph + IsSymm/IsLoopless ») a
remplacé, dans `Basic.lean` seulement, l'ancien type bundlé `LooplessTemporalGraph V` (avec
champs `.symm`/`.loopless`) par un `TemporalGraph V` nu (juste `Adj`) plus deux prédicats
externes `IsSymm`/`IsLoopless`, dans le style déjà utilisé pour `IsSimple`/`IsClique`/`IsProper`.
Le reste du dépôt n'a pas encore été porté :

- Seuls `Init.lean` et `Basic.lean` compilent isolément (vérifié via `lake env lean <fichier>`).
- `NonemptyTemporalWalk.lean`, `TemporalWalk.lean`, `SubTemporalGraph.lean`,
  `Connectivity/Basic.lean`, `Connectivity/SubTemporalGraph.lean`, `Dismountability/Basic.lean`,
  `Dismountability/Operations.lean` référencent encore `LooplessTemporalGraph V` et ne
  compilent plus (ex. `Function expected at LooplessTemporalGraph but this term has type ?m.1`).
- Le fichier racine `TemporalGraph.lean` a en plus deux problèmes propres : il importe
  `TemporalGraph.Dismountability` (module inexistant — il faudrait `Dismountability.Basic` /
  `Dismountability.Operations`, ou un fichier agrégateur), et référence un troisième nom
  obsolète, `SimpleTemporalGraph`. `lake build` échoue dès cet import.

**Pattern à appliquer pour porter un fichier** : remplacer `G : LooplessTemporalGraph V` par
`G : TemporalGraph V`, et ajouter en hypothèse explicite `(hs : G.IsSymm)` / `(hl : G.IsLoopless)`
partout où l'ancien code utilisait les champs bundlés `.symm`/`.loopless` (voir comment
`Basic.lean` fait déjà pour `IsSimple`/`IsClique`/`IsProper` : ce sont des hypothèses passées
explicitement, jamais des champs de structure).

**Ordre de dépendance à respecter** pour porter le reste :
`NonemptyTemporalWalk` → `TemporalWalk` → `SubTemporalGraph` → `Connectivity/Basic` →
`Connectivity/SubTemporalGraph` → `Dismountability/Basic` → `Dismountability/Operations` →
`TemporalGraph.lean` (racine, à corriger ou à retirer de `defaultTargets` en attendant).

## Conventions de nommage/style observées

- Dot-notation façon Mathlib : `protected theorem Adj.ne`, `Adj.symm`, etc.
- Attributs `@[ext]`, `@[simp]`, `@[symm]` posés comme dans les fichiers `SimpleGraph`.
- Arêtes non orientées représentées par `Sym2 V` ; `EdgeSet : Set (Sym2 V × ℕ)`.
- Automatisation via la macro `aesop_temporal_graph`, qui utilise le rule-set aesop
  `LooplessTemporalGraph` déclaré dans `Init.lean` — ce nom de rule-set est resté sur l'ancien
  nom du type ; à renommer plus tard si on veut de la cohérence stricte, mais ce n'est pas
  bloquant (c'est juste une étiquette de rule-set, pas une référence de type).

## Repères papier ↔ code

Les commentaires numérotés dans `Dismountability/Basic.lean` renvoient à
Casteigts–Peters–Schoeters :

| Commentaire dans le code | Contenu |
|---|---|
| `-- Theorem 2.1` | `Dismountable` |
| `-- def 3.1` | `Vminus`, `Vplus`, `Vzero` |
| `-- lemma 3.1` | `partition_of_not_dismountable` |
| `-- lemma 3.2` | `vplus_ne_neighbor_of_not_twoHopHismountable`, `vminus_ne_neighbor_of_not_twoHopDismountable` |
| `-- lemma 3.4` | `vzero_empty_of_not_twoHopDismountable` |

Toute nouvelle preuve visant un résultat du papier (ou d'un résultat récent connexe) devrait
garder cette convention : un commentaire citant le numéro exact du théorème/lemme visé.

## Commandes utiles

- Le toolchain Lean (`lean`, `lake`, `elan`) est dans `~/.elan/bin`, pas forcément sur le `PATH`
  d'un sous-shell : utiliser `~/.elan/bin/lake ...` au besoin.
- `lake build` : build complet (échoue actuellement à cause de `TemporalGraph.lean`, voir
  ci-dessus).
- `lake env lean TemporalGraph/<Fichier>.lean` : typechecker un fichier isolé sans dépendre du
  reste — utile tant que le refactor n'est pas terminé.
- CI GitHub Actions existante (ne pas modifier sans raison) : `lean_action_ci.yml` (build +
  docgen), `create-release.yml` (tag de release sur changement de `lean-toolchain`),
  `update.yml` (PR/issue automatique sur mise à jour Mathlib).
