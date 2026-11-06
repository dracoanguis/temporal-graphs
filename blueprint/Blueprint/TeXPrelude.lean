import Verso
import VersoManual
import VersoBlueprint
import TemporalGraph

open Informal

/-! TeX macros shared by every chapter (KaTeX in HTML, lualatex in the PDF). -/

tex_prelude r#"
\providecommand{\N}{\mathbb{N}}
"#
