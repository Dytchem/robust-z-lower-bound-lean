# 论文源码

"Explicit finite-order lower bounds for high-order robust composite $Z$ rotations"。

| 文件 | 作用 |
|---|---|
| `main.tex` | 正文：标题块、摘要、§I–§VII、附录 A/B |
| `verification.tex` | §VIII 机器验证、Lean 对照表、资源表 |
| `discussion.tex` | §IX 讨论与结论 |
| `num_tables.tex` | 表 III 表体（由数据生成，勿手改） |
| `refs.bib` | 参考文献，BibTeX，样式 `apsrev4-2.bst` |
| `fignum_num.pdf`, `figphys.pdf` | 图 1、图 2 |
| `build.sh` | 编译脚本，一次产出两个 PDF |

```sh
./build.sh
```

- `main.pdf` — APS 投稿版：REVTeX 4.2 `[aps,pra,preprint]`，单栏、双倍行距。
- `main_arxiv.pdf` — 同一份源码加 `tightenlines`，单倍行距，arXiv 用这个（arXiv 不收双倍行距 referee 版）。

编译产生的 `.aux`、`.log`、`.out`、`.blg`、`mainNotes.bib` 是中间文件，可随时删。

arXiv 上传：`main.tex verification.tex discussion.tex num_tables.tex refs.bib fignum_num.pdf figphys.pdf`，或附上 `main.bbl`。APS 要求 BibTeX 预先跑过（`build.sh` 已包含）。

数值数据、角度表与复算脚本在数据集里，不在本目录：<https://show.dytchem.cn/files/code.zip>。
