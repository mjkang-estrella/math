import NReplay016
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_31095 : CNF.NClause := [(55,false),(49,false),(31,false),(43,true),(122,true)]
theorem der_31095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31095 :=
  CNF.rup_sound cl_31095 [cl_25214,cl_31094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25214 v h) (hints_cons _ _ _ (der_31094 v h) (by intro d hd; cases hd)))
def cl_31098 : CNF.NClause := [(37,false),(55,false),(31,false),(57,true),(122,true)]
theorem der_31098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31098 :=
  CNF.rup_sound cl_31098 [cl_25217,cl_31094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25217 v h) (hints_cons _ _ _ (der_31094 v h) (by intro d hd; cases hd)))
def cl_31100 : CNF.NClause := [(37,false),(49,false),(43,false),(31,false),(122,true)]
theorem der_31100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31100 :=
  CNF.rup_sound cl_31100 [cl_25219,cl_25211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25219 v h) (hints_cons _ _ _ (der_25211 v h) (by intro d hd; cases hd)))
def cl_31101 : CNF.NClause := [(49,false),(37,true),(43,false),(57,true),(122,true)]
theorem der_31101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31101 :=
  CNF.rup_sound cl_31101 [cl_25220,cl_25212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25220 v h) (hints_cons _ _ _ (der_25212 v h) (by intro d hd; cases hd)))
def cl_31104 : CNF.NClause := [(37,false),(49,true),(43,false),(55,true),(122,true)]
theorem der_31104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31104 :=
  CNF.rup_sound cl_31104 [cl_25223,cl_31091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25223 v h) (hints_cons _ _ _ (der_31091 v h) (by intro d hd; cases hd)))
def cl_31108 : CNF.NClause := [(41,false),(51,false),(56,false),(31,false),(123,true)]
theorem der_31108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31108 :=
  CNF.rup_sound cl_31108 [cl_25230,cl_25229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25230 v h) (hints_cons _ _ _ (der_25229 v h) (by intro d hd; cases hd)))
def cl_31112 : CNF.NClause := [(36,false),(46,false),(56,false),(31,false),(123,true)]
theorem der_31112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31112 :=
  CNF.rup_sound cl_31112 [cl_25235,cl_25233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25235 v h) (hints_cons _ _ _ (der_25233 v h) (by intro d hd; cases hd)))
def cl_31113 : CNF.NClause := [(46,false),(56,false),(31,false),(41,true),(123,true)]
theorem der_31113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31113 :=
  CNF.rup_sound cl_31113 [cl_25236,cl_31112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25236 v h) (hints_cons _ _ _ (der_31112 v h) (by intro d hd; cases hd)))
def cl_31114 : CNF.NClause := [(41,false),(36,false),(56,false),(31,false),(123,true)]
theorem der_31114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31114 :=
  CNF.rup_sound cl_31114 [cl_25237,cl_31112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25237 v h) (hints_cons _ _ _ (der_31112 v h) (by intro d hd; cases hd)))
def cl_31118 : CNF.NClause := [(41,false),(51,false),(46,false),(56,true),(123,true)]
theorem der_31118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31118 :=
  CNF.rup_sound cl_31118 [cl_25242,cl_25241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25242 v h) (hints_cons _ _ _ (der_25241 v h) (by intro d hd; cases hd)))
def cl_31119 : CNF.NClause := [(51,false),(46,false),(36,true),(56,true),(123,true)]
theorem der_31119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31119 :=
  CNF.rup_sound cl_31119 [cl_25244,cl_31118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25244 v h) (hints_cons _ _ _ (der_31118 v h) (by intro d hd; cases hd)))
def cl_31121 : CNF.NClause := [(41,false),(51,false),(31,false),(46,true),(123,true)]
theorem der_31121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31121 :=
  CNF.rup_sound cl_31121 [cl_25246,cl_31108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25246 v h) (hints_cons _ _ _ (der_31108 v h) (by intro d hd; cases hd)))
def cl_31124 : CNF.NClause := [(41,false),(36,false),(46,false),(31,false),(123,true)]
theorem der_31124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31124 :=
  CNF.rup_sound cl_31124 [cl_25249,cl_31114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25249 v h) (hints_cons _ _ _ (der_31114 v h) (by intro d hd; cases hd)))
def cl_31126 : CNF.NClause := [(36,false),(46,false),(31,false),(41,true),(123,true)]
theorem der_31126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31126 :=
  CNF.rup_sound cl_31126 [cl_25251,cl_25243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25251 v h) (hints_cons _ _ _ (der_25243 v h) (by intro d hd; cases hd)))
def cl_31127 : CNF.NClause := [(46,false),(31,false),(36,true),(56,true),(123,true)]
theorem der_31127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31127 :=
  CNF.rup_sound cl_31127 [cl_25252,cl_31119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25252 v h) (hints_cons _ _ _ (der_31119 v h) (by intro d hd; cases hd)))
def cl_31128 : CNF.NClause := [(41,false),(36,false),(31,false),(46,true),(123,true)]
theorem der_31128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31128 :=
  CNF.rup_sound cl_31128 [cl_25253,cl_31114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25253 v h) (hints_cons _ _ _ (der_31114 v h) (by intro d hd; cases hd)))
def cl_31131 : CNF.NClause := [(35,false),(61,false),(34,false),(33,true),(118,true)]
theorem der_31131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31131 :=
  CNF.rup_sound cl_31131 [cl_25259,cl_25258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25259 v h) (hints_cons _ _ _ (der_25258 v h) (by intro d hd; cases hd)))
def cl_31132 : CNF.NClause := [(35,false),(61,false),(33,true),(32,true),(118,true)]
theorem der_31132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31132 :=
  CNF.rup_sound cl_31132 [cl_25260,cl_31131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25260 v h) (hints_cons _ _ _ (der_31131 v h) (by intro d hd; cases hd)))
def cl_31133 : CNF.NClause := [(61,false),(34,false),(33,false),(32,true),(118,true)]
theorem der_31133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31133 :=
  CNF.rup_sound cl_31133 [cl_25262,cl_25257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25262 v h) (hints_cons _ _ _ (der_25257 v h) (by intro d hd; cases hd)))
def cl_31135 : CNF.NClause := [(61,false),(34,false),(32,true),(35,true),(118,true)]
theorem der_31135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31135 :=
  CNF.rup_sound cl_31135 [cl_25264,cl_31133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25264 v h) (hints_cons _ _ _ (der_31133 v h) (by intro d hd; cases hd)))
def cl_31140 : CNF.NClause := [(41,false),(61,false),(42,false),(43,true),(103,true)]
theorem der_31140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31140 :=
  CNF.rup_sound cl_31140 [cl_25272,cl_23879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25272 v h) (hints_cons _ _ _ (der_23879 v h) (by intro d hd; cases hd)))
def cl_31142 : CNF.NClause := [(39,false),(36,false),(37,false),(38,true),(113,true)]
theorem der_31142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31142 :=
  CNF.rup_sound cl_31142 [cl_25275,cl_30802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25275 v h) (hints_cons _ _ _ (der_30802 v h) (by intro d hd; cases hd)))
def cl_31143 : CNF.NClause := [(39,false),(36,false),(37,false),(38,false),(113,true)]
theorem der_31143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31143 :=
  CNF.rup_sound cl_31143 [cl_25276,cl_23715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25276 v h) (hints_cons _ _ _ (der_23715 v h) (by intro d hd; cases hd)))
def cl_31145 : CNF.NClause := [(51,false),(61,false),(52,false),(55,true),(98,true)]
theorem der_31145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31145 :=
  CNF.rup_sound cl_31145 [cl_25278,cl_30059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25278 v h) (hints_cons _ _ _ (der_30059 v h) (by intro d hd; cases hd)))
def cl_31146 : CNF.NClause := [(36,false),(55,true),(47,false),(33,false),(115,true)]
theorem der_31146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31146 :=
  CNF.rup_sound cl_31146 [cl_25281,cl_30844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25281 v h) (hints_cons _ _ _ (der_30844 v h) (by intro d hd; cases hd)))
def cl_31151 : CNF.NClause := [(41,false),(32,false),(48,false),(58,true),(107,true)]
theorem der_31151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31151 :=
  CNF.rup_sound cl_31151 [cl_25287,cl_30741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25287 v h) (hints_cons _ _ _ (der_30741 v h) (by intro d hd; cases hd)))
def cl_31152 : CNF.NClause := [(51,false),(52,false),(53,false),(55,true),(98,true)]
theorem der_31152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31152 :=
  CNF.rup_sound cl_31152 [cl_25288,cl_31145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25288 v h) (hints_cons _ _ _ (der_31145 v h) (by intro d hd; cases hd)))
def cl_31153 : CNF.NClause := [(37,false),(122,true),(31,true),(55,true),(43,false)]
theorem der_31153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31153 :=
  CNF.rup_sound cl_31153 [cl_25290,cl_25289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25290 v h) (hints_cons _ _ _ (der_25289 v h) (by intro d hd; cases hd)))
def cl_31156 : CNF.NClause := [(35,false),(50,false),(40,true),(56,true),(94,true)]
theorem der_31156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31156 :=
  CNF.rup_sound cl_31156 [cl_25293,cl_23858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25293 v h) (hints_cons _ _ _ (der_23858 v h) (by intro d hd; cases hd)))
def cl_31160 : CNF.NClause := [(48,false),(49,false),(47,true),(46,true),(108,true)]
theorem der_31160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31160 :=
  CNF.rup_sound cl_31160 [cl_25300,cl_23773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25300 v h) (hints_cons _ _ _ (der_23773 v h) (by intro d hd; cases hd)))
def cl_31161 : CNF.NClause := [(61,false),(47,false),(49,false),(46,true),(108,true)]
theorem der_31161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31161 :=
  CNF.rup_sound cl_31161 [cl_25301,cl_25299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25301 v h) (hints_cons _ _ _ (der_25299 v h) (by intro d hd; cases hd)))
def cl_31162 : CNF.NClause := [(48,false),(61,false),(47,false),(46,true),(108,true)]
theorem der_31162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31162 :=
  CNF.rup_sound cl_31162 [cl_25302,cl_25299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25302 v h) (hints_cons _ _ _ (der_25299 v h) (by intro d hd; cases hd)))
def cl_31164 : CNF.NClause := [(61,false),(47,false),(48,true),(46,true),(108,true)]
theorem der_31164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31164 :=
  CNF.rup_sound cl_31164 [cl_25304,cl_31161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25304 v h) (hints_cons _ _ _ (der_31161 v h) (by intro d hd; cases hd)))
def cl_31165 : CNF.NClause := [(48,false),(50,false),(49,false),(46,true),(108,true)]
theorem der_31165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31165 :=
  CNF.rup_sound cl_31165 [cl_25305,cl_31160] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25305 v h) (hints_cons _ _ _ (der_31160 v h) (by intro d hd; cases hd)))
def cl_31166 : CNF.NClause := [(50,false),(47,false),(49,false),(46,true),(108,true)]
theorem der_31166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31166 :=
  CNF.rup_sound cl_31166 [cl_25306,cl_31165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25306 v h) (hints_cons _ _ _ (der_31165 v h) (by intro d hd; cases hd)))
def cl_31168 : CNF.NClause := [(50,false),(47,false),(48,true),(46,true),(108,true)]
theorem der_31168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31168 :=
  CNF.rup_sound cl_31168 [cl_25308,cl_31166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25308 v h) (hints_cons _ _ _ (der_31166 v h) (by intro d hd; cases hd)))
def cl_31169 : CNF.NClause := [(48,false),(49,false),(46,true),(50,true),(108,true)]
theorem der_31169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31169 :=
  CNF.rup_sound cl_31169 [cl_25309,cl_31160] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25309 v h) (hints_cons _ _ _ (der_31160 v h) (by intro d hd; cases hd)))
def cl_31170 : CNF.NClause := [(47,false),(49,false),(48,true),(46,true),(108,true)]
theorem der_31170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31170 :=
  CNF.rup_sound cl_31170 [cl_25310,cl_31164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25310 v h) (hints_cons _ _ _ (der_31164 v h) (by intro d hd; cases hd)))
def cl_31171 : CNF.NClause := [(48,false),(47,false),(49,true),(46,true),(108,true)]
theorem der_31171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31171 :=
  CNF.rup_sound cl_31171 [cl_25311,cl_31162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25311 v h) (hints_cons _ _ _ (der_31162 v h) (by intro d hd; cases hd)))
def cl_31172 : CNF.NClause := [(32,false),(59,false),(43,false),(54,false),(112,true)]
theorem der_31172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31172 :=
  CNF.rup_sound cl_31172 [cl_25313,cl_23905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25313 v h) (hints_cons _ _ _ (der_23905 v h) (by intro d hd; cases hd)))
def cl_31173 : CNF.NClause := [(32,false),(59,false),(43,false),(46,true),(112,true)]
theorem der_31173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31173 :=
  CNF.rup_sound cl_31173 [cl_25314,cl_31172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25314 v h) (hints_cons _ _ _ (der_31172 v h) (by intro d hd; cases hd)))
def cl_31174 : CNF.NClause := [(32,false),(54,true),(46,true),(43,false),(112,true)]
theorem der_31174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31174 :=
  CNF.rup_sound cl_31174 [cl_25315,cl_31173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25315 v h) (hints_cons _ _ _ (der_31173 v h) (by intro d hd; cases hd)))
def cl_31175 : CNF.NClause := [(41,false),(51,false),(31,true),(56,true),(123,true)]
theorem der_31175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31175 :=
  CNF.rup_sound cl_31175 [cl_25316,cl_31118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25316 v h) (hints_cons _ _ _ (der_31118 v h) (by intro d hd; cases hd)))
def cl_31177 : CNF.NClause := [(42,false),(38,false),(34,false),(46,true),(111,true)]
theorem der_31177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31177 :=
  CNF.rup_sound cl_31177 [cl_25319,cl_25318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25319 v h) (hints_cons _ _ _ (der_25318 v h) (by intro d hd; cases hd)))
def cl_31179 : CNF.NClause := [(51,false),(49,true),(40,false),(33,false),(100,true)]
theorem der_31179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31179 :=
  CNF.rup_sound cl_31179 [cl_25324,cl_25320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25324 v h) (hints_cons _ _ _ (der_25320 v h) (by intro d hd; cases hd)))
def cl_31180 : CNF.NClause := [(40,false),(42,true),(49,true),(33,false),(100,true)]
theorem der_31180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31180 :=
  CNF.rup_sound cl_31180 [cl_25326,cl_31179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25326 v h) (hints_cons _ _ _ (der_31179 v h) (by intro d hd; cases hd)))
def cl_31184 : CNF.NClause := [(41,false),(45,false),(42,true),(43,true),(103,true)]
theorem der_31184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31184 :=
  CNF.rup_sound cl_31184 [cl_25331,cl_30123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25331 v h) (hints_cons _ _ _ (der_30123 v h) (by intro d hd; cases hd)))
def cl_31185 : CNF.NClause := [(41,false),(44,false),(45,true),(42,true),(103,true)]
theorem der_31185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31185 :=
  CNF.rup_sound cl_31185 [cl_25332,cl_23699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25332 v h) (hints_cons _ _ _ (der_23699 v h) (by intro d hd; cases hd)))
def cl_31186 : CNF.NClause := [(60,false),(46,false),(55,false),(34,false),(111,true)]
theorem der_31186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31186 :=
  CNF.rup_sound cl_31186 [cl_25334,cl_23717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25334 v h) (hints_cons _ _ _ (der_23717 v h) (by intro d hd; cases hd)))
def cl_31187 : CNF.NClause := [(60,false),(55,false),(34,false),(46,true),(111,true)]
theorem der_31187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31187 :=
  CNF.rup_sound cl_31187 [cl_25335,cl_30056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25335 v h) (hints_cons _ _ _ (der_30056 v h) (by intro d hd; cases hd)))
def cl_31188 : CNF.NClause := [(60,false),(38,false),(46,false),(34,false),(111,true)]
theorem der_31188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31188 :=
  CNF.rup_sound cl_31188 [cl_25336,cl_31186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25336 v h) (hints_cons _ _ _ (der_31186 v h) (by intro d hd; cases hd)))
def cl_31189 : CNF.NClause := [(60,false),(38,false),(34,false),(55,true),(111,true)]
theorem der_31189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31189 :=
  CNF.rup_sound cl_31189 [cl_25337,cl_31188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25337 v h) (hints_cons _ _ _ (der_31188 v h) (by intro d hd; cases hd)))
def cl_31190 : CNF.NClause := [(38,false),(46,false),(55,false),(34,false),(111,true)]
theorem der_31190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31190 :=
  CNF.rup_sound cl_31190 [cl_25338,cl_31186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25338 v h) (hints_cons _ _ _ (der_31186 v h) (by intro d hd; cases hd)))
def cl_31191 : CNF.NClause := [(38,false),(55,false),(34,false),(60,true),(111,true)]
theorem der_31191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31191 :=
  CNF.rup_sound cl_31191 [cl_25339,cl_31190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25339 v h) (hints_cons _ _ _ (der_31190 v h) (by intro d hd; cases hd)))
def cl_31192 : CNF.NClause := [(38,false),(46,false),(34,false),(60,true),(111,true)]
theorem der_31192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31192 :=
  CNF.rup_sound cl_31192 [cl_25340,cl_31190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25340 v h) (hints_cons _ _ _ (der_31190 v h) (by intro d hd; cases hd)))
def cl_31193 : CNF.NClause := [(38,false),(34,false),(46,true),(55,true),(111,true)]
theorem der_31193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31193 :=
  CNF.rup_sound cl_31193 [cl_25341,cl_31189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25341 v h) (hints_cons _ _ _ (der_31189 v h) (by intro d hd; cases hd)))
def cl_31196 : CNF.NClause := [(35,false),(57,false),(48,false),(36,false),(114,true)]
theorem der_31196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31196 :=
  CNF.rup_sound cl_31196 [cl_25344,cl_30979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25344 v h) (hints_cons _ _ _ (der_30979 v h) (by intro d hd; cases hd)))
def cl_31197 : CNF.NClause := [(35,false),(57,false),(36,false),(42,true),(114,true)]
theorem der_31197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31197 :=
  CNF.rup_sound cl_31197 [cl_25345,cl_31196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25345 v h) (hints_cons _ _ _ (der_31196 v h) (by intro d hd; cases hd)))
def cl_31198 : CNF.NClause := [(35,false),(48,false),(54,false),(42,true),(114,true)]
theorem der_31198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31198 :=
  CNF.rup_sound cl_31198 [cl_25346,cl_30859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25346 v h) (hints_cons _ _ _ (der_30859 v h) (by intro d hd; cases hd)))
def cl_31199 : CNF.NClause := [(35,false),(54,false),(42,true),(48,true),(114,true)]
theorem der_31199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31199 :=
  CNF.rup_sound cl_31199 [cl_25347,cl_30861] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25347 v h) (hints_cons _ _ _ (der_30861 v h) (by intro d hd; cases hd)))
def cl_31200 : CNF.NClause := [(35,false),(48,false),(36,false),(54,true),(114,true)]
theorem der_31200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31200 :=
  CNF.rup_sound cl_31200 [cl_25348,cl_31196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25348 v h) (hints_cons _ _ _ (der_31196 v h) (by intro d hd; cases hd)))
def cl_31201 : CNF.NClause := [(35,false),(36,false),(42,true),(48,true),(114,true)]
theorem der_31201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31201 :=
  CNF.rup_sound cl_31201 [cl_25349,cl_31199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25349 v h) (hints_cons _ _ _ (der_31199 v h) (by intro d hd; cases hd)))
def cl_31202 : CNF.NClause := [(59,false),(50,false),(53,false),(31,true),(121,true)]
theorem der_31202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31202 :=
  CNF.rup_sound cl_31202 [cl_25350,cl_31060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25350 v h) (hints_cons _ _ _ (der_31060 v h) (by intro d hd; cases hd)))
def cl_31203 : CNF.NClause := [(59,false),(121,true),(31,true),(42,true),(53,false)]
theorem der_31203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31203 :=
  CNF.rup_sound cl_31203 [cl_25351,cl_31202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25351 v h) (hints_cons _ _ _ (der_31202 v h) (by intro d hd; cases hd)))
def cl_31204 : CNF.NClause := [(59,false),(50,false),(31,true),(53,true),(121,true)]
theorem der_31204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31204 :=
  CNF.rup_sound cl_31204 [cl_25352,cl_23743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25352 v h) (hints_cons _ _ _ (der_23743 v h) (by intro d hd; cases hd)))
def cl_31205 : CNF.NClause := [(59,false),(39,false),(31,true),(53,true),(121,true)]
theorem der_31205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31205 :=
  CNF.rup_sound cl_31205 [cl_25353,cl_23760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25353 v h) (hints_cons _ _ _ (der_23760 v h) (by intro d hd; cases hd)))
def cl_31206 : CNF.NClause := [(39,false),(59,true),(42,true),(53,false),(121,true)]
theorem der_31206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31206 :=
  CNF.rup_sound cl_31206 [cl_25355,cl_25354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25355 v h) (hints_cons _ _ _ (der_25354 v h) (by intro d hd; cases hd)))
def cl_31207 : CNF.NClause := [(50,false),(39,false),(31,true),(53,true),(121,true)]
theorem der_31207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31207 :=
  CNF.rup_sound cl_31207 [cl_25356,cl_31204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25356 v h) (hints_cons _ _ _ (der_31204 v h) (by intro d hd; cases hd)))
def cl_31208 : CNF.NClause := [(41,false),(44,false),(43,false),(42,true),(103,true)]
theorem der_31208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31208 :=
  CNF.rup_sound cl_31208 [cl_25357,cl_23699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25357 v h) (hints_cons _ _ _ (der_23699 v h) (by intro d hd; cases hd)))
def cl_31209 : CNF.NClause := [(51,false),(58,false),(33,false),(49,true),(100,true)]
theorem der_31209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31209 :=
  CNF.rup_sound cl_31209 [cl_25359,cl_31179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25359 v h) (hints_cons _ _ _ (der_31179 v h) (by intro d hd; cases hd)))
def cl_31210 : CNF.NClause := [(58,false),(42,true),(49,false),(33,false),(100,true)]
theorem der_31210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31210 :=
  CNF.rup_sound cl_31210 [cl_25360,cl_25358] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25360 v h) (hints_cons _ _ _ (der_25358 v h) (by intro d hd; cases hd)))
def cl_31211 : CNF.NClause := [(58,false),(49,true),(33,false),(42,true),(100,true)]
theorem der_31211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31211 :=
  CNF.rup_sound cl_31211 [cl_25361,cl_31209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25361 v h) (hints_cons _ _ _ (der_31209 v h) (by intro d hd; cases hd)))
def cl_31212 : CNF.NClause := [(51,false),(49,false),(33,false),(58,true),(100,true)]
theorem der_31212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31212 :=
  CNF.rup_sound cl_31212 [cl_25362,cl_25323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25362 v h) (hints_cons _ _ _ (der_25323 v h) (by intro d hd; cases hd)))
def cl_31213 : CNF.NClause := [(51,false),(49,true),(33,false),(58,true),(100,true)]
theorem der_31213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31213 :=
  CNF.rup_sound cl_31213 [cl_25363,cl_30111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25363 v h) (hints_cons _ _ _ (der_30111 v h) (by intro d hd; cases hd)))
def cl_31214 : CNF.NClause := [(49,false),(58,true),(42,true),(33,false),(100,true)]
theorem der_31214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31214 :=
  CNF.rup_sound cl_31214 [cl_25364,cl_31212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25364 v h) (hints_cons _ _ _ (der_31212 v h) (by intro d hd; cases hd)))
def cl_31215 : CNF.NClause := [(32,false),(52,false),(47,false),(42,true),(97,true)]
theorem der_31215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31215 :=
  CNF.rup_sound cl_31215 [cl_25365,cl_30774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25365 v h) (hints_cons _ _ _ (der_30774 v h) (by intro d hd; cases hd)))
def cl_31216 : CNF.NClause := [(32,false),(37,false),(52,false),(42,true),(97,true)]
theorem der_31216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31216 :=
  CNF.rup_sound cl_31216 [cl_25366,cl_31215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25366 v h) (hints_cons _ _ _ (der_31215 v h) (by intro d hd; cases hd)))
def cl_31217 : CNF.NClause := [(32,false),(37,false),(56,true),(52,true),(97,true)]
theorem der_31217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31217 :=
  CNF.rup_sound cl_31217 [cl_25368,cl_25367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25368 v h) (hints_cons _ _ _ (der_25367 v h) (by intro d hd; cases hd)))
def cl_31218 : CNF.NClause := [(46,false),(55,false),(34,false),(60,true),(111,true)]
theorem der_31218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31218 :=
  CNF.rup_sound cl_31218 [cl_25369,cl_31190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25369 v h) (hints_cons _ _ _ (der_31190 v h) (by intro d hd; cases hd)))
def cl_31219 : CNF.NClause := [(55,false),(34,false),(38,true),(46,true),(111,true)]
theorem der_31219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31219 :=
  CNF.rup_sound cl_31219 [cl_25370,cl_30055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25370 v h) (hints_cons _ _ _ (der_30055 v h) (by intro d hd; cases hd)))
def cl_31221 : CNF.NClause := [(54,false),(44,false),(56,false),(34,true),(96,true)]
theorem der_31221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31221 :=
  CNF.rup_sound cl_31221 [cl_25375,cl_25374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25375 v h) (hints_cons _ _ _ (der_25374 v h) (by intro d hd; cases hd)))
def cl_31225 : CNF.NClause := [(39,false),(56,false),(49,false),(34,true),(96,true)]
theorem der_31225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31225 :=
  CNF.rup_sound cl_31225 [cl_25380,cl_25378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25380 v h) (hints_cons _ _ _ (der_25378 v h) (by intro d hd; cases hd)))
def cl_31227 : CNF.NClause := [(44,false),(56,false),(49,true),(54,true),(96,true)]
theorem der_31227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31227 :=
  CNF.rup_sound cl_31227 [cl_25383,cl_25382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25383 v h) (hints_cons _ _ _ (der_25382 v h) (by intro d hd; cases hd)))
def cl_31228 : CNF.NClause := [(39,false),(56,false),(44,true),(34,true),(96,true)]
theorem der_31228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31228 :=
  CNF.rup_sound cl_31228 [cl_25384,cl_31225] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25384 v h) (hints_cons _ _ _ (der_31225 v h) (by intro d hd; cases hd)))
def cl_31229 : CNF.NClause := [(39,false),(54,false),(49,false),(34,true),(96,true)]
theorem der_31229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31229 :=
  CNF.rup_sound cl_31229 [cl_25387,cl_25385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25387 v h) (hints_cons _ _ _ (der_25385 v h) (by intro d hd; cases hd)))
def cl_31230 : CNF.NClause := [(54,false),(49,false),(44,true),(34,true),(96,true)]
theorem der_31230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31230 :=
  CNF.rup_sound cl_31230 [cl_25388,cl_31229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25388 v h) (hints_cons _ _ _ (der_31229 v h) (by intro d hd; cases hd)))
def cl_31231 : CNF.NClause := [(39,false),(54,false),(44,false),(34,true),(96,true)]
theorem der_31231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31231 :=
  CNF.rup_sound cl_31231 [cl_25389,cl_25385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25389 v h) (hints_cons _ _ _ (der_25385 v h) (by intro d hd; cases hd)))
def cl_31232 : CNF.NClause := [(54,false),(44,false),(39,true),(56,true),(96,true)]
theorem der_31232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31232 :=
  CNF.rup_sound cl_31232 [cl_25390,cl_25386] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25390 v h) (hints_cons _ _ _ (der_25386 v h) (by intro d hd; cases hd)))
def cl_31233 : CNF.NClause := [(39,false),(54,false),(44,true),(34,true),(96,true)]
theorem der_31233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31233 :=
  CNF.rup_sound cl_31233 [cl_25391,cl_31230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25391 v h) (hints_cons _ _ _ (der_31230 v h) (by intro d hd; cases hd)))
def cl_31234 : CNF.NClause := [(44,false),(49,false),(39,true),(56,true),(96,true)]
theorem der_31234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31234 :=
  CNF.rup_sound cl_31234 [cl_25393,cl_31232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25393 v h) (hints_cons _ _ _ (der_31232 v h) (by intro d hd; cases hd)))
def cl_31235 : CNF.NClause := [(39,false),(49,false),(44,true),(34,true),(96,true)]
theorem der_31235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31235 :=
  CNF.rup_sound cl_31235 [cl_25394,cl_31233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25394 v h) (hints_cons _ _ _ (der_31233 v h) (by intro d hd; cases hd)))
def cl_31236 : CNF.NClause := [(39,false),(44,false),(49,true),(54,true),(96,true)]
theorem der_31236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31236 :=
  CNF.rup_sound cl_31236 [cl_25395,cl_31227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25395 v h) (hints_cons _ _ _ (der_31227 v h) (by intro d hd; cases hd)))
def cl_31237 : CNF.NClause := [(59,false),(51,false),(48,false),(45,false),(101,true)]
theorem der_31237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31237 :=
  CNF.rup_sound cl_31237 [cl_25397,cl_25396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25397 v h) (hints_cons _ _ _ (der_25396 v h) (by intro d hd; cases hd)))
def cl_31239 : CNF.NClause := [(59,false),(51,false),(48,false),(37,true),(101,true)]
theorem der_31239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31239 :=
  CNF.rup_sound cl_31239 [cl_25399,cl_31237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25399 v h) (hints_cons _ _ _ (der_31237 v h) (by intro d hd; cases hd)))
def cl_31240 : CNF.NClause := [(59,false),(51,false),(45,false),(37,true),(101,true)]
theorem der_31240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31240 :=
  CNF.rup_sound cl_31240 [cl_25401,cl_24805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25401 v h) (hints_cons _ _ _ (der_24805 v h) (by intro d hd; cases hd)))
def cl_31242 : CNF.NClause := [(59,false),(51,false),(37,true),(48,true),(101,true)]
theorem der_31242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31242 :=
  CNF.rup_sound cl_31242 [cl_25403,cl_31240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25403 v h) (hints_cons _ _ _ (der_31240 v h) (by intro d hd; cases hd)))
def cl_31243 : CNF.NClause := [(59,false),(48,false),(45,false),(37,true),(101,true)]
theorem der_31243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31243 :=
  CNF.rup_sound cl_31243 [cl_25405,cl_30790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25405 v h) (hints_cons _ _ _ (der_30790 v h) (by intro d hd; cases hd)))
def cl_31244 : CNF.NClause := [(59,false),(48,false),(37,false),(34,true),(101,true)]
theorem der_31244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31244 :=
  CNF.rup_sound cl_31244 [cl_25406,cl_25404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25406 v h) (hints_cons _ _ _ (der_25404 v h) (by intro d hd; cases hd)))
def cl_31245 : CNF.NClause := [(59,false),(48,false),(45,true),(37,true),(101,true)]
theorem der_31245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31245 :=
  CNF.rup_sound cl_31245 [cl_25407,cl_31239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25407 v h) (hints_cons _ _ _ (der_31239 v h) (by intro d hd; cases hd)))
def cl_31246 : CNF.NClause := [(59,false),(37,false),(45,false),(34,true),(101,true)]
theorem der_31246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31246 :=
  CNF.rup_sound cl_31246 [cl_25408,cl_31244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25408 v h) (hints_cons _ _ _ (der_31244 v h) (by intro d hd; cases hd)))
def cl_31247 : CNF.NClause := [(59,false),(45,false),(37,true),(48,true),(101,true)]
theorem der_31247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31247 :=
  CNF.rup_sound cl_31247 [cl_25409,cl_31240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25409 v h) (hints_cons _ _ _ (der_31240 v h) (by intro d hd; cases hd)))
def cl_31248 : CNF.NClause := [(59,false),(37,false),(45,true),(34,true),(101,true)]
theorem der_31248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31248 :=
  CNF.rup_sound cl_31248 [cl_25410,cl_31244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25410 v h) (hints_cons _ _ _ (der_31244 v h) (by intro d hd; cases hd)))
def cl_31249 : CNF.NClause := [(51,false),(48,false),(45,false),(37,true),(101,true)]
theorem der_31249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31249 :=
  CNF.rup_sound cl_31249 [cl_25412,cl_24811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25412 v h) (hints_cons _ _ _ (der_24811 v h) (by intro d hd; cases hd)))
def cl_31250 : CNF.NClause := [(51,false),(48,false),(37,false),(34,true),(101,true)]
theorem der_31250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31250 :=
  CNF.rup_sound cl_31250 [cl_25413,cl_25411] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25413 v h) (hints_cons _ _ _ (der_25411 v h) (by intro d hd; cases hd)))
def cl_31251 : CNF.NClause := [(51,false),(48,false),(45,true),(37,true),(101,true)]
theorem der_31251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31251 :=
  CNF.rup_sound cl_31251 [cl_25414,cl_30792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25414 v h) (hints_cons _ _ _ (der_30792 v h) (by intro d hd; cases hd)))
def cl_31252 : CNF.NClause := [(51,false),(37,false),(45,false),(34,true),(101,true)]
theorem der_31252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31252 :=
  CNF.rup_sound cl_31252 [cl_25415,cl_25411] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25415 v h) (hints_cons _ _ _ (der_25411 v h) (by intro d hd; cases hd)))
def cl_31253 : CNF.NClause := [(51,false),(45,false),(37,true),(59,true),(101,true)]
theorem der_31253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31253 :=
  CNF.rup_sound cl_31253 [cl_25416,cl_30793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25416 v h) (hints_cons _ _ _ (der_30793 v h) (by intro d hd; cases hd)))
def cl_31254 : CNF.NClause := [(51,false),(37,false),(48,true),(34,true),(101,true)]
theorem der_31254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31254 :=
  CNF.rup_sound cl_31254 [cl_25417,cl_31252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25417 v h) (hints_cons _ _ _ (der_31252 v h) (by intro d hd; cases hd)))
def cl_31255 : CNF.NClause := [(48,false),(37,false),(45,false),(34,true),(101,true)]
theorem der_31255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31255 :=
  CNF.rup_sound cl_31255 [cl_25418,cl_31246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25418 v h) (hints_cons _ _ _ (der_31246 v h) (by intro d hd; cases hd)))
def cl_31256 : CNF.NClause := [(48,false),(45,false),(37,true),(34,true),(101,true)]
theorem der_31256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31256 :=
  CNF.rup_sound cl_31256 [cl_25419,cl_31249] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25419 v h) (hints_cons _ _ _ (der_31249 v h) (by intro d hd; cases hd)))
def cl_31257 : CNF.NClause := [(48,false),(37,false),(45,true),(34,true),(101,true)]
theorem der_31257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31257 :=
  CNF.rup_sound cl_31257 [cl_25420,cl_31248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25420 v h) (hints_cons _ _ _ (der_31248 v h) (by intro d hd; cases hd)))
def cl_31258 : CNF.NClause := [(37,false),(45,false),(48,true),(34,true),(101,true)]
theorem der_31258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31258 :=
  CNF.rup_sound cl_31258 [cl_25421,cl_31252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25421 v h) (hints_cons _ _ _ (der_31252 v h) (by intro d hd; cases hd)))
def cl_31259 : CNF.NClause := [(41,false),(57,false),(47,false),(53,false),(106,true)]
theorem der_31259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31259 :=
  CNF.rup_sound cl_31259 [cl_25423,cl_30107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25423 v h) (hints_cons _ _ _ (der_30107 v h) (by intro d hd; cases hd)))
def cl_31261 : CNF.NClause := [(41,false),(57,false),(40,false),(53,false),(106,true)]
theorem der_31261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31261 :=
  CNF.rup_sound cl_31261 [cl_25426,cl_30099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25426 v h) (hints_cons _ _ _ (der_30099 v h) (by intro d hd; cases hd)))
def cl_31262 : CNF.NClause := [(41,false),(57,false),(53,false),(34,true),(106,true)]
theorem der_31262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31262 :=
  CNF.rup_sound cl_31262 [cl_25427,cl_31261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25427 v h) (hints_cons _ _ _ (der_31261 v h) (by intro d hd; cases hd)))
def cl_31264 : CNF.NClause := [(57,false),(40,true),(53,false),(34,true),(106,true)]
theorem der_31264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31264 :=
  CNF.rup_sound cl_31264 [cl_25429,cl_31262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25429 v h) (hints_cons _ _ _ (der_31262 v h) (by intro d hd; cases hd)))
def cl_31265 : CNF.NClause := [(41,false),(57,false),(40,false),(47,false),(106,true)]
theorem der_31265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31265 :=
  CNF.rup_sound cl_31265 [cl_25430,cl_25422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25430 v h) (hints_cons _ _ _ (der_25422 v h) (by intro d hd; cases hd)))
def cl_31267 : CNF.NClause := [(57,false),(40,false),(47,false),(34,true),(106,true)]
theorem der_31267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31267 :=
  CNF.rup_sound cl_31267 [cl_25432,cl_31265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25432 v h) (hints_cons _ _ _ (der_31265 v h) (by intro d hd; cases hd)))
def cl_31268 : CNF.NClause := [(57,false),(47,false),(34,true),(41,true),(106,true)]
theorem der_31268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31268 :=
  CNF.rup_sound cl_31268 [cl_25433,cl_31267] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25433 v h) (hints_cons _ _ _ (der_31267 v h) (by intro d hd; cases hd)))
def cl_31269 : CNF.NClause := [(41,false),(57,false),(40,false),(53,true),(106,true)]
theorem der_31269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31269 :=
  CNF.rup_sound cl_31269 [cl_25434,cl_31265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25434 v h) (hints_cons _ _ _ (der_31265 v h) (by intro d hd; cases hd)))
def cl_31270 : CNF.NClause := [(41,false),(57,false),(47,true),(40,true),(106,true)]
theorem der_31270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31270 :=
  CNF.rup_sound cl_31270 [cl_25435,cl_23819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25435 v h) (hints_cons _ _ _ (der_23819 v h) (by intro d hd; cases hd)))
def cl_31271 : CNF.NClause := [(57,false),(40,false),(34,true),(41,true),(106,true)]
theorem der_31271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31271 :=
  CNF.rup_sound cl_31271 [cl_25436,cl_31267] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25436 v h) (hints_cons _ _ _ (der_31267 v h) (by intro d hd; cases hd)))
def cl_31272 : CNF.NClause := [(41,false),(47,false),(53,false),(34,true),(106,true)]
theorem der_31272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31272 :=
  CNF.rup_sound cl_31272 [cl_25438,cl_25437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25438 v h) (hints_cons _ _ _ (der_25437 v h) (by intro d hd; cases hd)))
def cl_31273 : CNF.NClause := [(40,false),(47,false),(53,false),(34,true),(106,true)]
theorem der_31273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31273 :=
  CNF.rup_sound cl_31273 [cl_25439,cl_25437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25439 v h) (hints_cons _ _ _ (der_25437 v h) (by intro d hd; cases hd)))
def cl_31274 : CNF.NClause := [(47,false),(40,true),(53,false),(34,true),(106,true)]
theorem der_31274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31274 :=
  CNF.rup_sound cl_31274 [cl_25440,cl_31272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25440 v h) (hints_cons _ _ _ (der_31272 v h) (by intro d hd; cases hd)))
def cl_31275 : CNF.NClause := [(41,false),(40,false),(53,false),(34,true),(106,true)]
theorem der_31275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31275 :=
  CNF.rup_sound cl_31275 [cl_25441,cl_25437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25441 v h) (hints_cons _ _ _ (der_25437 v h) (by intro d hd; cases hd)))
def cl_31276 : CNF.NClause := [(41,false),(47,true),(53,false),(34,true),(106,true)]
theorem der_31276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31276 :=
  CNF.rup_sound cl_31276 [cl_25442,cl_31275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25442 v h) (hints_cons _ _ _ (der_31275 v h) (by intro d hd; cases hd)))
def cl_31277 : CNF.NClause := [(40,false),(47,true),(34,true),(53,false),(106,true)]
theorem der_31277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31277 :=
  CNF.rup_sound cl_31277 [cl_25443,cl_31275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25443 v h) (hints_cons _ _ _ (der_31275 v h) (by intro d hd; cases hd)))
def cl_31278 : CNF.NClause := [(41,false),(40,false),(47,false),(53,true),(106,true)]
theorem der_31278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31278 :=
  CNF.rup_sound cl_31278 [cl_25444,cl_31269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25444 v h) (hints_cons _ _ _ (der_31269 v h) (by intro d hd; cases hd)))
def cl_31279 : CNF.NClause := [(41,false),(47,false),(40,true),(53,true),(106,true)]
theorem der_31279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31279 :=
  CNF.rup_sound cl_31279 [cl_25445,cl_30063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25445 v h) (hints_cons _ _ _ (der_30063 v h) (by intro d hd; cases hd)))
def cl_31280 : CNF.NClause := [(40,false),(47,false),(53,true),(34,true),(106,true)]
theorem der_31280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31280 :=
  CNF.rup_sound cl_31280 [cl_25446,cl_31278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25446 v h) (hints_cons _ _ _ (der_31278 v h) (by intro d hd; cases hd)))
def cl_31281 : CNF.NClause := [(41,false),(40,false),(47,true),(53,true),(106,true)]
theorem der_31281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31281 :=
  CNF.rup_sound cl_31281 [cl_25447,cl_31269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25447 v h) (hints_cons _ _ _ (der_31269 v h) (by intro d hd; cases hd)))
def cl_31282 : CNF.NClause := [(42,false),(60,false),(46,false),(55,false),(111,true)]
theorem der_31282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31282 :=
  CNF.rup_sound cl_31282 [cl_25449,cl_25448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25449 v h) (hints_cons _ _ _ (der_25448 v h) (by intro d hd; cases hd)))
def cl_31283 : CNF.NClause := [(60,false),(38,false),(46,false),(55,false),(111,true)]
theorem der_31283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31283 :=
  CNF.rup_sound cl_31283 [cl_25450,cl_25448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25450 v h) (hints_cons _ _ _ (der_25448 v h) (by intro d hd; cases hd)))
def cl_31284 : CNF.NClause := [(60,false),(46,false),(55,false),(42,true),(111,true)]
theorem der_31284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31284 :=
  CNF.rup_sound cl_31284 [cl_25451,cl_31283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25451 v h) (hints_cons _ _ _ (der_31283 v h) (by intro d hd; cases hd)))
def cl_31285 : CNF.NClause := [(42,false),(60,false),(38,false),(55,false),(111,true)]
theorem der_31285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31285 :=
  CNF.rup_sound cl_31285 [cl_25452,cl_25448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25452 v h) (hints_cons _ _ _ (der_25448 v h) (by intro d hd; cases hd)))
def cl_31288 : CNF.NClause := [(60,false),(55,false),(42,true),(34,true),(111,true)]
theorem der_31288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31288 :=
  CNF.rup_sound cl_31288 [cl_25455,cl_31284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25455 v h) (hints_cons _ _ _ (der_31284 v h) (by intro d hd; cases hd)))
def cl_31289 : CNF.NClause := [(42,false),(60,false),(38,false),(46,false),(111,true)]
theorem der_31289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31289 :=
  CNF.rup_sound cl_31289 [cl_25456,cl_25448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25456 v h) (hints_cons _ _ _ (der_25448 v h) (by intro d hd; cases hd)))
def cl_31290 : CNF.NClause := [(42,false),(60,false),(46,false),(38,true),(111,true)]
theorem der_31290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31290 :=
  CNF.rup_sound cl_31290 [cl_25457,cl_31282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25457 v h) (hints_cons _ _ _ (der_31282 v h) (by intro d hd; cases hd)))
def cl_31291 : CNF.NClause := [(60,false),(38,false),(46,false),(42,true),(111,true)]
theorem der_31291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31291 :=
  CNF.rup_sound cl_31291 [cl_25458,cl_31283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25458 v h) (hints_cons _ _ _ (der_31283 v h) (by intro d hd; cases hd)))
def cl_31292 : CNF.NClause := [(60,false),(46,false),(42,true),(55,true),(111,true)]
theorem der_31292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31292 :=
  CNF.rup_sound cl_31292 [cl_25459,cl_31291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25459 v h) (hints_cons _ _ _ (der_31291 v h) (by intro d hd; cases hd)))
def cl_31293 : CNF.NClause := [(42,false),(60,false),(38,false),(55,true),(111,true)]
theorem der_31293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31293 :=
  CNF.rup_sound cl_31293 [cl_25460,cl_31289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25460 v h) (hints_cons _ _ _ (der_31289 v h) (by intro d hd; cases hd)))
def cl_31294 : CNF.NClause := [(42,false),(60,false),(46,true),(55,true),(111,true)]
theorem der_31294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31294 :=
  CNF.rup_sound cl_31294 [cl_25461,cl_31293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25461 v h) (hints_cons _ _ _ (der_31293 v h) (by intro d hd; cases hd)))
def cl_31295 : CNF.NClause := [(60,false),(38,false),(42,true),(34,true),(111,true)]
theorem der_31295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31295 :=
  CNF.rup_sound cl_31295 [cl_25462,cl_31291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25462 v h) (hints_cons _ _ _ (der_31291 v h) (by intro d hd; cases hd)))
def cl_31296 : CNF.NClause := [(42,false),(38,false),(46,false),(55,false),(111,true)]
theorem der_31296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31296 :=
  CNF.rup_sound cl_31296 [cl_25463,cl_25448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25463 v h) (hints_cons _ _ _ (der_25448 v h) (by intro d hd; cases hd)))
def cl_31297 : CNF.NClause := [(42,false),(46,false),(55,false),(38,true),(111,true)]
theorem der_31297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31297 :=
  CNF.rup_sound cl_31297 [cl_25464,cl_31282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25464 v h) (hints_cons _ _ _ (der_31282 v h) (by intro d hd; cases hd)))
def cl_31299 : CNF.NClause := [(46,false),(55,false),(42,true),(34,true),(111,true)]
theorem der_31299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31299 :=
  CNF.rup_sound cl_31299 [cl_25466,cl_31284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25466 v h) (hints_cons _ _ _ (der_31284 v h) (by intro d hd; cases hd)))
def cl_31300 : CNF.NClause := [(42,false),(38,false),(55,false),(46,true),(111,true)]
theorem der_31300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31300 :=
  CNF.rup_sound cl_31300 [cl_25467,cl_31285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25467 v h) (hints_cons _ _ _ (der_31285 v h) (by intro d hd; cases hd)))
def cl_31301 : CNF.NClause := [(42,false),(55,false),(38,true),(34,true),(111,true)]
theorem der_31301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31301 :=
  CNF.rup_sound cl_31301 [cl_25468,cl_31297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25468 v h) (hints_cons _ _ _ (der_31297 v h) (by intro d hd; cases hd)))
def cl_31302 : CNF.NClause := [(38,false),(55,false),(42,true),(34,true),(111,true)]
theorem der_31302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31302 :=
  CNF.rup_sound cl_31302 [cl_25469,cl_31299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25469 v h) (hints_cons _ _ _ (der_31299 v h) (by intro d hd; cases hd)))
def cl_31303 : CNF.NClause := [(42,false),(38,false),(46,false),(55,true),(111,true)]
theorem der_31303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31303 :=
  CNF.rup_sound cl_31303 [cl_25470,cl_31289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25470 v h) (hints_cons _ _ _ (der_31289 v h) (by intro d hd; cases hd)))
def cl_31304 : CNF.NClause := [(42,false),(46,false),(38,true),(55,true),(111,true)]
theorem der_31304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31304 :=
  CNF.rup_sound cl_31304 [cl_25471,cl_31290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25471 v h) (hints_cons _ _ _ (der_31290 v h) (by intro d hd; cases hd)))
def cl_31305 : CNF.NClause := [(38,false),(46,false),(42,true),(34,true),(111,true)]
theorem der_31305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31305 :=
  CNF.rup_sound cl_31305 [cl_25472,cl_31295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25472 v h) (hints_cons _ _ _ (der_31295 v h) (by intro d hd; cases hd)))
def cl_31306 : CNF.NClause := [(42,false),(38,false),(46,true),(55,true),(111,true)]
theorem der_31306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31306 :=
  CNF.rup_sound cl_31306 [cl_25473,cl_31293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25473 v h) (hints_cons _ _ _ (der_31293 v h) (by intro d hd; cases hd)))
def cl_31307 : CNF.NClause := [(50,false),(58,false),(52,false),(36,true),(116,true)]
theorem der_31307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31307 :=
  CNF.rup_sound cl_31307 [cl_25476,cl_25474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25476 v h) (hints_cons _ _ _ (der_25474 v h) (by intro d hd; cases hd)))
def cl_31308 : CNF.NClause := [(58,false),(52,false),(43,false),(36,true),(116,true)]
theorem der_31308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31308 :=
  CNF.rup_sound cl_31308 [cl_25478,cl_31307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25478 v h) (hints_cons _ _ _ (der_31307 v h) (by intro d hd; cases hd)))
def cl_31309 : CNF.NClause := [(58,false),(36,false),(52,false),(34,true),(116,true)]
theorem der_31309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31309 :=
  CNF.rup_sound cl_31309 [cl_25479,cl_25477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25479 v h) (hints_cons _ _ _ (der_25477 v h) (by intro d hd; cases hd)))
def cl_31310 : CNF.NClause := [(58,false),(52,false),(36,true),(50,true),(116,true)]
theorem der_31310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31310 :=
  CNF.rup_sound cl_31310 [cl_25480,cl_31308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25480 v h) (hints_cons _ _ _ (der_31308 v h) (by intro d hd; cases hd)))
def cl_31311 : CNF.NClause := [(50,false),(58,false),(43,false),(52,true),(116,true)]
theorem der_31311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31311 :=
  CNF.rup_sound cl_31311 [cl_25482,cl_25481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25482 v h) (hints_cons _ _ _ (der_25481 v h) (by intro d hd; cases hd)))
def cl_31312 : CNF.NClause := [(50,false),(58,false),(36,true),(43,true),(116,true)]
theorem der_31312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31312 :=
  CNF.rup_sound cl_31312 [cl_25484,cl_30871] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25484 v h) (hints_cons _ _ _ (der_30871 v h) (by intro d hd; cases hd)))
def cl_31313 : CNF.NClause := [(58,false),(36,false),(43,false),(34,true),(116,true)]
theorem der_31313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31313 :=
  CNF.rup_sound cl_31313 [cl_25485,cl_25477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25485 v h) (hints_cons _ _ _ (der_25477 v h) (by intro d hd; cases hd)))
def cl_31314 : CNF.NClause := [(58,false),(36,true),(43,false),(50,true),(116,true)]
theorem der_31314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31314 :=
  CNF.rup_sound cl_31314 [cl_25486,cl_30872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25486 v h) (hints_cons _ _ _ (der_30872 v h) (by intro d hd; cases hd)))
def cl_31315 : CNF.NClause := [(58,false),(36,false),(43,true),(34,true),(116,true)]
theorem der_31315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31315 :=
  CNF.rup_sound cl_31315 [cl_25487,cl_25483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25487 v h) (hints_cons _ _ _ (der_25483 v h) (by intro d hd; cases hd)))
def cl_31316 : CNF.NClause := [(50,false),(52,false),(43,false),(36,true),(116,true)]
theorem der_31316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31316 :=
  CNF.rup_sound cl_31316 [cl_25489,cl_30868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25489 v h) (hints_cons _ _ _ (der_30868 v h) (by intro d hd; cases hd)))
def cl_31317 : CNF.NClause := [(50,false),(36,false),(52,false),(34,true),(116,true)]
theorem der_31317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31317 :=
  CNF.rup_sound cl_31317 [cl_25490,cl_25488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25490 v h) (hints_cons _ _ _ (der_25488 v h) (by intro d hd; cases hd)))
def cl_31318 : CNF.NClause := [(50,false),(52,false),(36,true),(58,true),(116,true)]
theorem der_31318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31318 :=
  CNF.rup_sound cl_31318 [cl_25491,cl_31316] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25491 v h) (hints_cons _ _ _ (der_31316 v h) (by intro d hd; cases hd)))
def cl_31320 : CNF.NClause := [(52,false),(36,true),(43,false),(50,true),(116,true)]
theorem der_31320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31320 :=
  CNF.rup_sound cl_31320 [cl_25493,cl_30868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25493 v h) (hints_cons _ _ _ (der_30868 v h) (by intro d hd; cases hd)))
def cl_31321 : CNF.NClause := [(36,false),(52,false),(58,true),(34,true),(116,true)]
theorem der_31321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31321 :=
  CNF.rup_sound cl_31321 [cl_25494,cl_31317] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25494 v h) (hints_cons _ _ _ (der_31317 v h) (by intro d hd; cases hd)))
def cl_31322 : CNF.NClause := [(50,false),(52,true),(36,false),(43,false),(116,true)]
theorem der_31322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31322 :=
  CNF.rup_sound cl_31322 [cl_25495,cl_31311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25495 v h) (hints_cons _ _ _ (der_31311 v h) (by intro d hd; cases hd)))
def cl_31323 : CNF.NClause := [(50,false),(36,true),(43,false),(58,true),(116,true)]
theorem der_31323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31323 :=
  CNF.rup_sound cl_31323 [cl_25496,cl_31316] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25496 v h) (hints_cons _ _ _ (der_31316 v h) (by intro d hd; cases hd)))
def cl_31324 : CNF.NClause := [(50,false),(36,false),(43,true),(34,true),(116,true)]
theorem der_31324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31324 :=
  CNF.rup_sound cl_31324 [cl_25497,cl_25483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25497 v h) (hints_cons _ _ _ (der_25483 v h) (by intro d hd; cases hd)))
def cl_31325 : CNF.NClause := [(36,false),(34,true),(43,false),(50,true),(116,true)]
theorem der_31325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31325 :=
  CNF.rup_sound cl_31325 [cl_25498,cl_31313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25498 v h) (hints_cons _ _ _ (der_31313 v h) (by intro d hd; cases hd)))
def cl_31326 : CNF.NClause := [(35,false),(61,false),(34,true),(32,true),(118,true)]
theorem der_31326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31326 :=
  CNF.rup_sound cl_31326 [cl_25500,cl_31132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25500 v h) (hints_cons _ _ _ (der_31132 v h) (by intro d hd; cases hd)))
def cl_31331 : CNF.NClause := [(32,false),(35,false),(34,true),(33,true),(118,true)]
theorem der_31331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31331 :=
  CNF.rup_sound cl_31331 [cl_25505,cl_31000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25505 v h) (hints_cons _ _ _ (der_31000 v h) (by intro d hd; cases hd)))
def cl_31332 : CNF.NClause := [(35,false),(118,true),(34,true),(32,true),(33,false)]
theorem der_31332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31332 :=
  CNF.rup_sound cl_31332 [cl_25507,cl_30999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25507 v h) (hints_cons _ _ _ (der_30999 v h) (by intro d hd; cases hd)))
def cl_31333 : CNF.NClause := [(32,false),(34,true),(33,false),(35,true),(118,true)]
theorem der_31333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31333 :=
  CNF.rup_sound cl_31333 [cl_25508,cl_31005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25508 v h) (hints_cons _ _ _ (der_31005 v h) (by intro d hd; cases hd)))
def cl_31334 : CNF.NClause := [(35,false),(37,false),(46,true),(58,true),(109,true)]
theorem der_31334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31334 :=
  CNF.rup_sound cl_31334 [cl_25509,cl_30124] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25509 v h) (hints_cons _ _ _ (der_30124 v h) (by intro d hd; cases hd)))
def cl_31335 : CNF.NClause := [(56,false),(62,false),(92,false),(66,false),(65,false)]
theorem der_31335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31335 :=
  CNF.rup_sound cl_31335 [cl_25510,cl_25016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25510 v h) (hints_cons _ _ _ (der_25016 v h) (by intro d hd; cases hd)))
def cl_31336 : CNF.NClause := [(56,false),(92,false),(63,false),(62,false),(66,false)]
theorem der_31336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31336 :=
  CNF.rup_sound cl_31336 [cl_25511,cl_30717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25511 v h) (hints_cons _ _ _ (der_30717 v h) (by intro d hd; cases hd)))
def cl_31337 : CNF.NClause := [(56,false),(65,false),(66,true),(92,false),(62,false)]
theorem der_31337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31337 :=
  CNF.rup_sound cl_31337 [cl_25512,cl_30947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25512 v h) (hints_cons _ _ _ (der_30947 v h) (by intro d hd; cases hd)))
def cl_31338 : CNF.NClause := [(56,false),(66,true),(92,false),(63,false),(62,false)]
theorem der_31338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31338 :=
  CNF.rup_sound cl_31338 [cl_25513,cl_31337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25513 v h) (hints_cons _ _ _ (der_31337 v h) (by intro d hd; cases hd)))
def cl_31339 : CNF.NClause := [(56,false),(62,false),(66,false),(65,false),(92,true)]
theorem der_31339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31339 :=
  CNF.rup_sound cl_31339 [cl_25514,cl_30954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25514 v h) (hints_cons _ _ _ (der_30954 v h) (by intro d hd; cases hd)))
def cl_31340 : CNF.NClause := [(56,false),(92,true),(62,false),(66,false),(65,true)]
theorem der_31340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31340 :=
  CNF.rup_sound cl_31340 [cl_25515,cl_30954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25515 v h) (hints_cons _ _ _ (der_30954 v h) (by intro d hd; cases hd)))
def cl_31341 : CNF.NClause := [(56,false),(65,false),(66,true),(62,false),(92,true)]
theorem der_31341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31341 :=
  CNF.rup_sound cl_31341 [cl_25516,cl_30955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25516 v h) (hints_cons _ _ _ (der_30955 v h) (by intro d hd; cases hd)))
def cl_31342 : CNF.NClause := [(56,false),(62,false),(65,true),(63,false),(92,true)]
theorem der_31342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31342 :=
  CNF.rup_sound cl_31342 [cl_25517,cl_30720] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25517 v h) (hints_cons _ _ _ (der_30720 v h) (by intro d hd; cases hd)))
def cl_31343 : CNF.NClause := [(56,false),(92,false),(64,true),(63,true),(62,true)]
theorem der_31343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31343 :=
  CNF.rup_sound cl_31343 [cl_25519,cl_25518] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25519 v h) (hints_cons _ _ _ (der_25518 v h) (by intro d hd; cases hd)))
def cl_31344 : CNF.NClause := [(56,false),(92,true),(63,true),(66,false),(65,false)]
theorem der_31344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31344 :=
  CNF.rup_sound cl_31344 [cl_25520,cl_30962] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25520 v h) (hints_cons _ _ _ (der_30962 v h) (by intro d hd; cases hd)))
def cl_31345 : CNF.NClause := [(56,false),(92,true),(63,true),(65,false),(64,true)]
theorem der_31345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31345 :=
  CNF.rup_sound cl_31345 [cl_25521,cl_31344] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25521 v h) (hints_cons _ _ _ (der_31344 v h) (by intro d hd; cases hd)))
def cl_31346 : CNF.NClause := [(56,false),(65,false),(92,false),(63,false),(66,false)]
theorem der_31346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31346 :=
  CNF.rup_sound cl_31346 [cl_25522,cl_31336] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25522 v h) (hints_cons _ _ _ (der_31336 v h) (by intro d hd; cases hd)))
def cl_31347 : CNF.NClause := [(56,false),(92,false),(62,true),(63,false),(65,false)]
theorem der_31347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31347 :=
  CNF.rup_sound cl_31347 [cl_25524,cl_30722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25524 v h) (hints_cons _ _ _ (der_30722 v h) (by intro d hd; cases hd)))
def cl_31348 : CNF.NClause := [(56,false),(62,true),(64,true),(65,true),(92,false)]
theorem der_31348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31348 :=
  CNF.rup_sound cl_31348 [cl_25525,cl_25523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25525 v h) (hints_cons _ _ _ (der_25523 v h) (by intro d hd; cases hd)))
def cl_31349 : CNF.NClause := [(56,false),(62,true),(66,false),(65,false),(92,true)]
theorem der_31349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31349 :=
  CNF.rup_sound cl_31349 [cl_25526,cl_31344] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25526 v h) (hints_cons _ _ _ (der_31344 v h) (by intro d hd; cases hd)))
def cl_31350 : CNF.NClause := [(56,false),(62,true),(64,true),(65,true),(66,false)]
theorem der_31350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31350 :=
  CNF.rup_sound cl_31350 [cl_25527,cl_30719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25527 v h) (hints_cons _ _ _ (der_30719 v h) (by intro d hd; cases hd)))
def cl_31351 : CNF.NClause := [(56,false),(62,true),(63,false),(65,false),(92,true)]
theorem der_31351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31351 :=
  CNF.rup_sound cl_31351 [cl_25528,cl_31349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25528 v h) (hints_cons _ _ _ (der_31349 v h) (by intro d hd; cases hd)))
def cl_31352 : CNF.NClause := [(56,false),(65,true),(66,true),(63,false),(92,true)]
theorem der_31352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31352 :=
  CNF.rup_sound cl_31352 [cl_25529,cl_31342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25529 v h) (hints_cons _ _ _ (der_31342 v h) (by intro d hd; cases hd)))
def cl_31353 : CNF.NClause := [(57,false),(59,false),(61,false),(60,false),(93,true)]
theorem der_31353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31353 :=
  CNF.rup_sound cl_31353 [cl_25532,cl_25530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25532 v h) (hints_cons _ _ _ (der_25530 v h) (by intro d hd; cases hd)))
def cl_31356 : CNF.NClause := [(57,false),(61,false),(60,false),(58,true),(93,true)]
theorem der_31356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31356 :=
  CNF.rup_sound cl_31356 [cl_25536,cl_31353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25536 v h) (hints_cons _ _ _ (der_31353 v h) (by intro d hd; cases hd)))
def cl_31357 : CNF.NClause := [(61,false),(60,false),(56,false),(58,true),(93,true)]
theorem der_31357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31357 :=
  CNF.rup_sound cl_31357 [cl_25537,cl_31356] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25537 v h) (hints_cons _ _ _ (der_31356 v h) (by intro d hd; cases hd)))
def cl_31358 : CNF.NClause := [(57,false),(59,false),(61,false),(58,false),(93,true)]
theorem der_31358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31358 :=
  CNF.rup_sound cl_31358 [cl_25538,cl_25530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25538 v h) (hints_cons _ _ _ (der_25530 v h) (by intro d hd; cases hd)))
def cl_31360 : CNF.NClause := [(57,false),(59,false),(61,false),(58,true),(93,true)]
theorem der_31360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31360 :=
  CNF.rup_sound cl_31360 [cl_25540,cl_31356] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25540 v h) (hints_cons _ _ _ (der_31356 v h) (by intro d hd; cases hd)))
def cl_31362 : CNF.NClause := [(57,false),(61,false),(58,false),(56,false),(93,true)]
theorem der_31362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31362 :=
  CNF.rup_sound cl_31362 [cl_25542,cl_25534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25542 v h) (hints_cons _ _ _ (der_25534 v h) (by intro d hd; cases hd)))
def cl_31364 : CNF.NClause := [(57,false),(61,false),(58,true),(59,true),(93,true)]
theorem der_31364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31364 :=
  CNF.rup_sound cl_31364 [cl_25544,cl_31356] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25544 v h) (hints_cons _ _ _ (der_31356 v h) (by intro d hd; cases hd)))
def cl_31366 : CNF.NClause := [(57,false),(59,false),(60,false),(58,false),(93,true)]
theorem der_31366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31366 :=
  CNF.rup_sound cl_31366 [cl_25546,cl_31358] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25546 v h) (hints_cons _ _ _ (der_31358 v h) (by intro d hd; cases hd)))
def cl_31367 : CNF.NClause := [(59,false),(60,false),(58,false),(56,false),(93,true)]
theorem der_31367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31367 :=
  CNF.rup_sound cl_31367 [cl_25547,cl_31366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25547 v h) (hints_cons _ _ _ (der_31366 v h) (by intro d hd; cases hd)))
def cl_31368 : CNF.NClause := [(57,false),(59,false),(60,false),(56,false),(93,true)]
theorem der_31368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31368 :=
  CNF.rup_sound cl_31368 [cl_25548,cl_31366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25548 v h) (hints_cons _ _ _ (der_31366 v h) (by intro d hd; cases hd)))
def cl_31370 : CNF.NClause := [(57,false),(60,false),(58,false),(56,false),(93,true)]
theorem der_31370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31370 :=
  CNF.rup_sound cl_31370 [cl_25550,cl_31367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25550 v h) (hints_cons _ _ _ (der_31367 v h) (by intro d hd; cases hd)))
def cl_31371 : CNF.NClause := [(60,false),(58,false),(56,false),(57,true),(93,true)]
theorem der_31371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31371 :=
  CNF.rup_sound cl_31371 [cl_25551,cl_31367] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25551 v h) (hints_cons _ _ _ (der_31367 v h) (by intro d hd; cases hd)))
def cl_31372 : CNF.NClause := [(57,false),(60,false),(58,true),(59,true),(93,true)]
theorem der_31372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31372 :=
  CNF.rup_sound cl_31372 [cl_25552,cl_31356] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25552 v h) (hints_cons _ _ _ (der_31356 v h) (by intro d hd; cases hd)))
def cl_31374 : CNF.NClause := [(57,false),(59,false),(58,false),(61,true),(93,true)]
theorem der_31374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31374 :=
  CNF.rup_sound cl_31374 [cl_25554,cl_31366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25554 v h) (hints_cons _ _ _ (der_31366 v h) (by intro d hd; cases hd)))
def cl_31376 : CNF.NClause := [(57,false),(59,false),(60,true),(61,true),(93,true)]
theorem der_31376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31376 :=
  CNF.rup_sound cl_31376 [cl_25556,cl_31374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25556 v h) (hints_cons _ _ _ (der_31374 v h) (by intro d hd; cases hd)))
def cl_31378 : CNF.NClause := [(57,false),(58,false),(56,false),(60,true),(93,true)]
theorem der_31378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31378 :=
  CNF.rup_sound cl_31378 [cl_25558,cl_31362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25558 v h) (hints_cons _ _ _ (der_31362 v h) (by intro d hd; cases hd)))
def cl_31381 : CNF.NClause := [(41,false),(51,false),(36,false),(46,false),(123,true)]
theorem der_31381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31381 :=
  CNF.rup_sound cl_31381 [cl_25561,cl_31124] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25561 v h) (hints_cons _ _ _ (der_31124 v h) (by intro d hd; cases hd)))
def cl_31382 : CNF.NClause := [(41,false),(51,false),(46,false),(31,true),(123,true)]
theorem der_31382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31382 :=
  CNF.rup_sound cl_31382 [cl_25562,cl_31381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25562 v h) (hints_cons _ _ _ (der_31381 v h) (by intro d hd; cases hd)))
def cl_31383 : CNF.NClause := [(51,false),(46,false),(31,true),(36,true),(123,true)]
theorem der_31383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31383 :=
  CNF.rup_sound cl_31383 [cl_25563,cl_31382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25563 v h) (hints_cons _ _ _ (der_31382 v h) (by intro d hd; cases hd)))
def cl_31384 : CNF.NClause := [(39,false),(34,false),(44,false),(54,true),(96,true)]
theorem der_31384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31384 :=
  CNF.rup_sound cl_31384 [cl_25567,cl_25063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25567 v h) (hints_cons _ _ _ (der_25063 v h) (by intro d hd; cases hd)))
def cl_31387 : CNF.NClause := [(41,false),(51,false),(36,false),(46,true),(123,true)]
theorem der_31387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31387 :=
  CNF.rup_sound cl_31387 [cl_25572,cl_31128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25572 v h) (hints_cons _ _ _ (der_31128 v h) (by intro d hd; cases hd)))
def cl_31392 : CNF.NClause := [(35,false),(40,false),(56,false),(45,true),(94,true)]
theorem der_31392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31392 :=
  CNF.rup_sound cl_31392 [cl_25578,cl_30053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25578 v h) (hints_cons _ _ _ (der_30053 v h) (by intro d hd; cases hd)))
def cl_31393 : CNF.NClause := [(35,false),(56,false),(45,true),(40,true),(94,true)]
theorem der_31393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31393 :=
  CNF.rup_sound cl_31393 [cl_25579,cl_30053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25579 v h) (hints_cons _ _ _ (der_30053 v h) (by intro d hd; cases hd)))
def cl_31396 : CNF.NClause := [(35,false),(40,false),(55,false),(56,false),(94,true)]
theorem der_31396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31396 :=
  CNF.rup_sound cl_31396 [cl_25583,cl_31392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25583 v h) (hints_cons _ _ _ (der_31392 v h) (by intro d hd; cases hd)))
def cl_31399 : CNF.NClause := [(41,false),(32,false),(58,false),(48,true),(107,true)]
theorem der_31399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31399 :=
  CNF.rup_sound cl_31399 [cl_25587,cl_30736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25587 v h) (hints_cons _ _ _ (der_30736 v h) (by intro d hd; cases hd)))
def cl_31400 : CNF.NClause := [(41,false),(32,false),(55,false),(48,true),(107,true)]
theorem der_31400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31400 :=
  CNF.rup_sound cl_31400 [cl_25588,cl_30739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25588 v h) (hints_cons _ _ _ (der_30739 v h) (by intro d hd; cases hd)))
def cl_31401 : CNF.NClause := [(35,false),(57,false),(42,false),(48,true),(114,true)]
theorem der_31401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31401 :=
  CNF.rup_sound cl_31401 [cl_25590,cl_30857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25590 v h) (hints_cons _ _ _ (der_30857 v h) (by intro d hd; cases hd)))
def cl_31402 : CNF.NClause := [(35,false),(36,false),(54,true),(57,true),(114,true)]
theorem der_31402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31402 :=
  CNF.rup_sound cl_31402 [cl_25591,cl_31200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25591 v h) (hints_cons _ _ _ (der_31200 v h) (by intro d hd; cases hd)))
def cl_31403 : CNF.NClause := [(59,false),(51,false),(34,false),(48,true),(101,true)]
theorem der_31403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31403 :=
  CNF.rup_sound cl_31403 [cl_25592,cl_30794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25592 v h) (hints_cons _ _ _ (der_30794 v h) (by intro d hd; cases hd)))
def cl_31405 : CNF.NClause := [(50,false),(61,false),(46,false),(49,true),(108,true)]
theorem der_31405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31405 :=
  CNF.rup_sound cl_31405 [cl_25594,cl_30097] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25594 v h) (hints_cons _ _ _ (der_30097 v h) (by intro d hd; cases hd)))
def cl_31407 : CNF.NClause := [(61,false),(46,false),(49,true),(50,true),(108,true)]
theorem der_31407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31407 :=
  CNF.rup_sound cl_31407 [cl_25596,cl_30097] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25596 v h) (hints_cons _ _ _ (der_30097 v h) (by intro d hd; cases hd)))
def cl_31408 : CNF.NClause := [(48,false),(56,false),(33,false),(53,false),(95,true)]
theorem der_31408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31408 :=
  CNF.rup_sound cl_31408 [cl_25598,cl_30087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25598 v h) (hints_cons _ _ _ (der_30087 v h) (by intro d hd; cases hd)))
def cl_31409 : CNF.NClause := [(56,false),(33,false),(53,false),(43,true),(95,true)]
theorem der_31409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31409 :=
  CNF.rup_sound cl_31409 [cl_25599,cl_30089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25599 v h) (hints_cons _ _ _ (der_30089 v h) (by intro d hd; cases hd)))
def cl_31411 : CNF.NClause := [(38,false),(56,false),(33,false),(48,true),(95,true)]
theorem der_31411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31411 :=
  CNF.rup_sound cl_31411 [cl_25601,cl_30084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25601 v h) (hints_cons _ _ _ (der_30084 v h) (by intro d hd; cases hd)))
def cl_31412 : CNF.NClause := [(48,false),(38,false),(33,false),(53,false),(95,true)]
theorem der_31412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31412 :=
  CNF.rup_sound cl_31412 [cl_25602,cl_31408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25602 v h) (hints_cons _ _ _ (der_31408 v h) (by intro d hd; cases hd)))
def cl_31414 : CNF.NClause := [(48,false),(38,false),(33,false),(53,true),(95,true)]
theorem der_31414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31414 :=
  CNF.rup_sound cl_31414 [cl_25604,cl_30090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25604 v h) (hints_cons _ _ _ (der_30090 v h) (by intro d hd; cases hd)))
def cl_31415 : CNF.NClause := [(38,false),(48,true),(33,false),(53,true),(95,true)]
theorem der_31415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31415 :=
  CNF.rup_sound cl_31415 [cl_25605,cl_31411] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25605 v h) (hints_cons _ _ _ (der_31411 v h) (by intro d hd; cases hd)))
def cl_31416 : CNF.NClause := [(32,false),(59,false),(54,false),(40,false),(112,true)]
theorem der_31416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31416 :=
  CNF.rup_sound cl_31416 [cl_25607,cl_25606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25607 v h) (hints_cons _ _ _ (der_25606 v h) (by intro d hd; cases hd)))
def cl_31417 : CNF.NClause := [(32,false),(59,false),(40,false),(46,false),(112,true)]
theorem der_31417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31417 :=
  CNF.rup_sound cl_31417 [cl_25608,cl_25606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25608 v h) (hints_cons _ _ _ (der_25606 v h) (by intro d hd; cases hd)))
def cl_31418 : CNF.NClause := [(32,false),(59,false),(40,false),(46,true),(112,true)]
theorem der_31418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31418 :=
  CNF.rup_sound cl_31418 [cl_25609,cl_31416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25609 v h) (hints_cons _ _ _ (der_31416 v h) (by intro d hd; cases hd)))
def cl_31419 : CNF.NClause := [(32,false),(54,false),(40,false),(43,true),(112,true)]
theorem der_31419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31419 :=
  CNF.rup_sound cl_31419 [cl_25611,cl_25610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25611 v h) (hints_cons _ _ _ (der_25610 v h) (by intro d hd; cases hd)))
def cl_31420 : CNF.NClause := [(32,false),(40,false),(46,false),(54,true),(112,true)]
theorem der_31420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31420 :=
  CNF.rup_sound cl_31420 [cl_25612,cl_31417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25612 v h) (hints_cons _ _ _ (der_31417 v h) (by intro d hd; cases hd)))
def cl_31421 : CNF.NClause := [(32,false),(40,false),(46,true),(54,true),(112,true)]
theorem der_31421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31421 :=
  CNF.rup_sound cl_31421 [cl_25613,cl_31418] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25613 v h) (hints_cons _ _ _ (der_31418 v h) (by intro d hd; cases hd)))
def cl_31422 : CNF.NClause := [(52,false),(34,false),(43,true),(50,true),(116,true)]
theorem der_31422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31422 :=
  CNF.rup_sound cl_31422 [cl_25615,cl_25614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25615 v h) (hints_cons _ _ _ (der_25614 v h) (by intro d hd; cases hd)))
def cl_31424 : CNF.NClause := [(41,false),(45,false),(44,true),(43,true),(103,true)]
theorem der_31424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31424 :=
  CNF.rup_sound cl_31424 [cl_25619,cl_23881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25619 v h) (hints_cons _ _ _ (der_23881 v h) (by intro d hd; cases hd)))
def cl_31425 : CNF.NClause := [(41,false),(44,false),(45,true),(43,true),(103,true)]
theorem der_31425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31425 :=
  CNF.rup_sound cl_31425 [cl_25620,cl_31185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25620 v h) (hints_cons _ _ _ (der_31185 v h) (by intro d hd; cases hd)))
def cl_31426 : CNF.NClause := [(35,false),(51,false),(60,false),(47,false),(99,true)]
theorem der_31426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31426 :=
  CNF.rup_sound cl_31426 [cl_25622,cl_30746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25622 v h) (hints_cons _ _ _ (der_30746 v h) (by intro d hd; cases hd)))
def cl_31427 : CNF.NClause := [(35,false),(51,false),(60,false),(47,true),(99,true)]
theorem der_31427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31427 :=
  CNF.rup_sound cl_31427 [cl_25623,cl_30745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25623 v h) (hints_cons _ _ _ (der_30745 v h) (by intro d hd; cases hd)))
def cl_31431 : CNF.NClause := [(35,false),(51,false),(39,false),(47,true),(99,true)]
theorem der_31431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31431 :=
  CNF.rup_sound cl_31431 [cl_25627,cl_31427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25627 v h) (hints_cons _ _ _ (der_31427 v h) (by intro d hd; cases hd)))
def cl_31432 : CNF.NClause := [(35,false),(47,false),(43,true),(51,true),(99,true)]
theorem der_31432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31432 :=
  CNF.rup_sound cl_31432 [cl_25628,cl_30753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25628 v h) (hints_cons _ _ _ (der_30753 v h) (by intro d hd; cases hd)))
def cl_31433 : CNF.NClause := [(35,false),(39,false),(43,true),(51,true),(99,true)]
theorem der_31433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31433 :=
  CNF.rup_sound cl_31433 [cl_25629,cl_31432] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25629 v h) (hints_cons _ _ _ (der_31432 v h) (by intro d hd; cases hd)))
def cl_31434 : CNF.NClause := [(57,false),(55,false),(49,false),(43,true),(122,true)]
theorem der_31434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31434 :=
  CNF.rup_sound cl_31434 [cl_25630,cl_31095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25630 v h) (hints_cons _ _ _ (der_31095 v h) (by intro d hd; cases hd)))
def cl_31435 : CNF.NClause := [(57,false),(37,false),(31,true),(55,true),(122,true)]
theorem der_31435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31435 :=
  CNF.rup_sound cl_31435 [cl_25631,cl_25289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25631 v h) (hints_cons _ _ _ (der_25289 v h) (by intro d hd; cases hd)))
def cl_31436 : CNF.NClause := [(37,false),(49,false),(31,true),(55,true),(122,true)]
theorem der_31436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31436 :=
  CNF.rup_sound cl_31436 [cl_25632,cl_31153] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25632 v h) (hints_cons _ _ _ (der_31153 v h) (by intro d hd; cases hd)))
def cl_31437 : CNF.NClause := [(58,false),(52,false),(34,false),(43,true),(116,true)]
theorem der_31437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31437 :=
  CNF.rup_sound cl_31437 [cl_25633,cl_25614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25633 v h) (hints_cons _ _ _ (der_25614 v h) (by intro d hd; cases hd)))
def cl_31438 : CNF.NClause := [(32,false),(59,false),(54,false),(46,false),(112,true)]
theorem der_31438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31438 :=
  CNF.rup_sound cl_31438 [cl_25634,cl_25606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25634 v h) (hints_cons _ _ _ (der_25606 v h) (by intro d hd; cases hd)))
def cl_31439 : CNF.NClause := [(32,false),(59,false),(54,false),(46,true),(112,true)]
theorem der_31439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31439 :=
  CNF.rup_sound cl_31439 [cl_25635,cl_31418] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25635 v h) (hints_cons _ _ _ (der_31418 v h) (by intro d hd; cases hd)))
def cl_31440 : CNF.NClause := [(32,false),(59,false),(46,false),(40,true),(112,true)]
theorem der_31440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31440 :=
  CNF.rup_sound cl_31440 [cl_25636,cl_31438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25636 v h) (hints_cons _ _ _ (der_31438 v h) (by intro d hd; cases hd)))
def cl_31441 : CNF.NClause := [(32,false),(59,false),(46,true),(54,true),(112,true)]
theorem der_31441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31441 :=
  CNF.rup_sound cl_31441 [cl_25637,cl_31418] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25637 v h) (hints_cons _ _ _ (der_31418 v h) (by intro d hd; cases hd)))
def cl_31442 : CNF.NClause := [(32,false),(54,false),(46,false),(43,true),(112,true)]
theorem der_31442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31442 :=
  CNF.rup_sound cl_31442 [cl_25638,cl_31438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25638 v h) (hints_cons _ _ _ (der_31438 v h) (by intro d hd; cases hd)))
def cl_31443 : CNF.NClause := [(32,false),(54,false),(43,true),(59,true),(112,true)]
theorem der_31443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31443 :=
  CNF.rup_sound cl_31443 [cl_25639,cl_31419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25639 v h) (hints_cons _ _ _ (der_31419 v h) (by intro d hd; cases hd)))
def cl_31444 : CNF.NClause := [(32,false),(46,false),(40,true),(54,true),(112,true)]
theorem der_31444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31444 :=
  CNF.rup_sound cl_31444 [cl_25640,cl_31440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25640 v h) (hints_cons _ _ _ (der_31440 v h) (by intro d hd; cases hd)))
def cl_31445 : CNF.NClause := [(57,false),(37,false),(49,true),(31,true),(122,true)]
theorem der_31445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31445 :=
  CNF.rup_sound cl_31445 [cl_25641,cl_23816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25641 v h) (hints_cons _ _ _ (der_23816 v h) (by intro d hd; cases hd)))
def cl_31446 : CNF.NClause := [(36,false),(34,false),(43,true),(50,true),(116,true)]
theorem der_31446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31446 :=
  CNF.rup_sound cl_31446 [cl_25642,cl_31422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25642 v h) (hints_cons _ _ _ (der_31422 v h) (by intro d hd; cases hd)))
def cl_31447 : CNF.NClause := [(50,false),(36,false),(34,false),(52,true),(116,true)]
theorem der_31447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31447 :=
  CNF.rup_sound cl_31447 [cl_25643,cl_25616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25643 v h) (hints_cons _ _ _ (der_25616 v h) (by intro d hd; cases hd)))
def cl_31448 : CNF.NClause := [(48,false),(38,true),(53,false),(95,true),(33,false)]
theorem der_31448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31448 :=
  CNF.rup_sound cl_31448 [cl_25644,cl_23783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25644 v h) (hints_cons _ _ _ (der_23783 v h) (by intro d hd; cases hd)))
def cl_31449 : CNF.NClause := [(95,true),(48,true),(53,false),(43,true),(33,false)]
theorem der_31449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31449 :=
  CNF.rup_sound cl_31449 [cl_25645,cl_31409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25645 v h) (hints_cons _ _ _ (der_31409 v h) (by intro d hd; cases hd)))
def cl_31450 : CNF.NClause := [(48,false),(95,true),(53,true),(33,false),(56,true)]
theorem der_31450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31450 :=
  CNF.rup_sound cl_31450 [cl_25646,cl_31414] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25646 v h) (hints_cons _ _ _ (der_31414 v h) (by intro d hd; cases hd)))
def cl_31451 : CNF.NClause := [(48,false),(56,false),(43,false),(53,false),(95,true)]
theorem der_31451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31451 :=
  CNF.rup_sound cl_31451 [cl_25648,cl_25647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25648 v h) (hints_cons _ _ _ (der_25647 v h) (by intro d hd; cases hd)))
def cl_31452 : CNF.NClause := [(48,false),(38,false),(53,false),(56,false),(95,true)]
theorem der_31452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31452 :=
  CNF.rup_sound cl_31452 [cl_25649,cl_25647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25649 v h) (hints_cons _ _ _ (der_25647 v h) (by intro d hd; cases hd)))
def cl_31454 : CNF.NClause := [(38,false),(56,false),(43,false),(53,false),(95,true)]
theorem der_31454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31454 :=
  CNF.rup_sound cl_31454 [cl_25651,cl_31451] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25651 v h) (hints_cons _ _ _ (der_31451 v h) (by intro d hd; cases hd)))
def cl_31455 : CNF.NClause := [(56,false),(38,true),(43,false),(53,false),(95,true)]
theorem der_31455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31455 :=
  CNF.rup_sound cl_31455 [cl_25652,cl_30089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25652 v h) (hints_cons _ _ _ (der_30089 v h) (by intro d hd; cases hd)))
def cl_31456 : CNF.NClause := [(38,false),(56,false),(53,false),(48,true),(95,true)]
theorem der_31456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31456 :=
  CNF.rup_sound cl_31456 [cl_25653,cl_31454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25653 v h) (hints_cons _ _ _ (der_31454 v h) (by intro d hd; cases hd)))
def cl_31458 : CNF.NClause := [(48,false),(38,false),(43,false),(56,false),(95,true)]
theorem der_31458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31458 :=
  CNF.rup_sound cl_31458 [cl_25655,cl_31454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25655 v h) (hints_cons _ _ _ (der_31454 v h) (by intro d hd; cases hd)))
def cl_31460 : CNF.NClause := [(48,false),(38,false),(56,false),(53,true),(95,true)]
theorem der_31460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31460 :=
  CNF.rup_sound cl_31460 [cl_25657,cl_31458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25657 v h) (hints_cons _ _ _ (der_31458 v h) (by intro d hd; cases hd)))
def cl_31463 : CNF.NClause := [(56,false),(38,true),(43,false),(53,true),(95,true)]
theorem der_31463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31463 :=
  CNF.rup_sound cl_31463 [cl_25660,cl_30091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25660 v h) (hints_cons _ _ _ (der_30091 v h) (by intro d hd; cases hd)))
def cl_31465 : CNF.NClause := [(48,false),(38,false),(43,false),(53,false),(95,true)]
theorem der_31465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31465 :=
  CNF.rup_sound cl_31465 [cl_25662,cl_31458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25662 v h) (hints_cons _ _ _ (der_31458 v h) (by intro d hd; cases hd)))
def cl_31466 : CNF.NClause := [(48,false),(38,true),(53,false),(95,true),(43,false)]
theorem der_31466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31466 :=
  CNF.rup_sound cl_31466 [cl_25663,cl_31455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25663 v h) (hints_cons _ _ _ (der_31455 v h) (by intro d hd; cases hd)))
def cl_31467 : CNF.NClause := [(48,false),(38,false),(53,false),(43,true),(95,true)]
theorem der_31467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31467 :=
  CNF.rup_sound cl_31467 [cl_25664,cl_31452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25664 v h) (hints_cons _ _ _ (der_31452 v h) (by intro d hd; cases hd)))
def cl_31468 : CNF.NClause := [(48,false),(53,false),(38,true),(56,true),(95,true)]
theorem der_31468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31468 :=
  CNF.rup_sound cl_31468 [cl_25665,cl_31466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25665 v h) (hints_cons _ _ _ (der_31466 v h) (by intro d hd; cases hd)))
def cl_31469 : CNF.NClause := [(38,false),(48,true),(43,false),(53,false),(95,true)]
theorem der_31469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31469 :=
  CNF.rup_sound cl_31469 [cl_25666,cl_31454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25666 v h) (hints_cons _ _ _ (der_31454 v h) (by intro d hd; cases hd)))
def cl_31470 : CNF.NClause := [(43,false),(53,false),(48,true),(56,true),(95,true)]
theorem der_31470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31470 :=
  CNF.rup_sound cl_31470 [cl_25667,cl_23274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25667 v h) (hints_cons _ _ _ (der_23274 v h) (by intro d hd; cases hd)))
def cl_31471 : CNF.NClause := [(38,false),(48,true),(53,false),(43,true),(95,true)]
theorem der_31471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31471 :=
  CNF.rup_sound cl_31471 [cl_25668,cl_31456] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25668 v h) (hints_cons _ _ _ (der_31456 v h) (by intro d hd; cases hd)))
def cl_31472 : CNF.NClause := [(48,false),(38,false),(43,false),(53,true),(95,true)]
theorem der_31472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31472 :=
  CNF.rup_sound cl_31472 [cl_25669,cl_30090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25669 v h) (hints_cons _ _ _ (der_30090 v h) (by intro d hd; cases hd)))
def cl_31473 : CNF.NClause := [(48,false),(38,true),(95,true),(53,true),(43,false)]
theorem der_31473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31473 :=
  CNF.rup_sound cl_31473 [cl_25670,cl_31463] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25670 v h) (hints_cons _ _ _ (der_31463 v h) (by intro d hd; cases hd)))
def cl_31474 : CNF.NClause := [(48,false),(38,false),(53,true),(43,true),(95,true)]
theorem der_31474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31474 :=
  CNF.rup_sound cl_31474 [cl_25671,cl_31460] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25671 v h) (hints_cons _ _ _ (der_31460 v h) (by intro d hd; cases hd)))
def cl_31475 : CNF.NClause := [(38,false),(43,false),(53,true),(56,true),(95,true)]
theorem der_31475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31475 :=
  CNF.rup_sound cl_31475 [cl_25672,cl_31472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25672 v h) (hints_cons _ _ _ (der_31472 v h) (by intro d hd; cases hd)))
def cl_31476 : CNF.NClause := [(51,false),(42,false),(58,false),(49,true),(100,true)]
theorem der_31476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31476 :=
  CNF.rup_sound cl_31476 [cl_25677,cl_25676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25677 v h) (hints_cons _ _ _ (der_25676 v h) (by intro d hd; cases hd)))
def cl_31477 : CNF.NClause := [(51,false),(58,false),(40,false),(49,true),(100,true)]
theorem der_31477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31477 :=
  CNF.rup_sound cl_31477 [cl_25678,cl_31476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25678 v h) (hints_cons _ _ _ (der_31476 v h) (by intro d hd; cases hd)))
def cl_31479 : CNF.NClause := [(58,false),(40,false),(49,false),(42,true),(100,true)]
theorem der_31479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31479 :=
  CNF.rup_sound cl_31479 [cl_25682,cl_25674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25682 v h) (hints_cons _ _ _ (der_25674 v h) (by intro d hd; cases hd)))
def cl_31480 : CNF.NClause := [(58,false),(49,false),(42,true),(51,true),(100,true)]
theorem der_31480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31480 :=
  CNF.rup_sound cl_31480 [cl_25683,cl_31479] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25683 v h) (hints_cons _ _ _ (der_31479 v h) (by intro d hd; cases hd)))
def cl_31481 : CNF.NClause := [(42,false),(58,false),(40,false),(33,true),(100,true)]
theorem der_31481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31481 :=
  CNF.rup_sound cl_31481 [cl_25684,cl_25680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25684 v h) (hints_cons _ _ _ (der_25680 v h) (by intro d hd; cases hd)))
def cl_31482 : CNF.NClause := [(42,false),(58,false),(33,true),(51,true),(100,true)]
theorem der_31482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31482 :=
  CNF.rup_sound cl_31482 [cl_25685,cl_31481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25685 v h) (hints_cons _ _ _ (der_31481 v h) (by intro d hd; cases hd)))
def cl_31483 : CNF.NClause := [(58,false),(40,false),(49,true),(42,true),(100,true)]
theorem der_31483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31483 :=
  CNF.rup_sound cl_31483 [cl_25686,cl_31477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25686 v h) (hints_cons _ _ _ (der_31477 v h) (by intro d hd; cases hd)))
def cl_31484 : CNF.NClause := [(51,false),(42,false),(49,false),(58,true),(100,true)]
theorem der_31484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31484 :=
  CNF.rup_sound cl_31484 [cl_25688,cl_25687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25688 v h) (hints_cons _ _ _ (der_25687 v h) (by intro d hd; cases hd)))
def cl_31485 : CNF.NClause := [(51,false),(40,false),(49,false),(42,true),(100,true)]
theorem der_31485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31485 :=
  CNF.rup_sound cl_31485 [cl_25689,cl_31479] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25689 v h) (hints_cons _ _ _ (der_31479 v h) (by intro d hd; cases hd)))
def cl_31486 : CNF.NClause := [(51,false),(49,false),(40,true),(33,true),(100,true)]
theorem der_31486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31486 :=
  CNF.rup_sound cl_31486 [cl_25690,cl_25675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25690 v h) (hints_cons _ _ _ (der_25675 v h) (by intro d hd; cases hd)))
def cl_31487 : CNF.NClause := [(51,false),(42,false),(40,false),(49,true),(100,true)]
theorem der_31487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31487 :=
  CNF.rup_sound cl_31487 [cl_25691,cl_31476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25691 v h) (hints_cons _ _ _ (der_31476 v h) (by intro d hd; cases hd)))
def cl_31488 : CNF.NClause := [(51,false),(42,false),(40,true),(33,true),(100,true)]
theorem der_31488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31488 :=
  CNF.rup_sound cl_31488 [cl_25692,cl_31486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25692 v h) (hints_cons _ _ _ (der_31486 v h) (by intro d hd; cases hd)))
def cl_31489 : CNF.NClause := [(51,false),(40,false),(49,true),(42,true),(100,true)]
theorem der_31489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31489 :=
  CNF.rup_sound cl_31489 [cl_25693,cl_31483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25693 v h) (hints_cons _ _ _ (der_31483 v h) (by intro d hd; cases hd)))
def cl_31490 : CNF.NClause := [(42,false),(49,false),(40,true),(33,true),(100,true)]
theorem der_31490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31490 :=
  CNF.rup_sound cl_31490 [cl_25695,cl_31488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25695 v h) (hints_cons _ _ _ (der_31488 v h) (by intro d hd; cases hd)))
def cl_31491 : CNF.NClause := [(40,false),(49,false),(42,true),(33,true),(100,true)]
theorem der_31491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31491 :=
  CNF.rup_sound cl_31491 [cl_25696,cl_31479] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25696 v h) (hints_cons _ _ _ (der_31479 v h) (by intro d hd; cases hd)))
def cl_31492 : CNF.NClause := [(42,false),(40,false),(49,true),(33,true),(100,true)]
theorem der_31492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31492 :=
  CNF.rup_sound cl_31492 [cl_25697,cl_31481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25697 v h) (hints_cons _ _ _ (der_31481 v h) (by intro d hd; cases hd)))
def cl_31493 : CNF.NClause := [(41,false),(50,false),(60,false),(54,false),(105,true)]
theorem der_31493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31493 :=
  CNF.rup_sound cl_31493 [cl_25699,cl_25698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25699 v h) (hints_cons _ _ _ (der_25698 v h) (by intro d hd; cases hd)))
def cl_31495 : CNF.NClause := [(41,false),(60,false),(54,false),(37,true),(105,true)]
theorem der_31495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31495 :=
  CNF.rup_sound cl_31495 [cl_25703,cl_31493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25703 v h) (hints_cons _ _ _ (der_31493 v h) (by intro d hd; cases hd)))
def cl_31496 : CNF.NClause := [(60,false),(54,false),(37,false),(33,true),(105,true)]
theorem der_31496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31496 :=
  CNF.rup_sound cl_31496 [cl_25704,cl_25702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25704 v h) (hints_cons _ _ _ (der_25702 v h) (by intro d hd; cases hd)))
def cl_31497 : CNF.NClause := [(60,false),(54,false),(37,true),(41,true),(105,true)]
theorem der_31497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31497 :=
  CNF.rup_sound cl_31497 [cl_25705,cl_30759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25705 v h) (hints_cons _ _ _ (der_30759 v h) (by intro d hd; cases hd)))
def cl_31498 : CNF.NClause := [(41,false),(50,false),(60,false),(37,false),(105,true)]
theorem der_31498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31498 :=
  CNF.rup_sound cl_31498 [cl_25706,cl_30975] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25706 v h) (hints_cons _ _ _ (der_30975 v h) (by intro d hd; cases hd)))
def cl_31499 : CNF.NClause := [(41,false),(50,false),(60,false),(54,true),(105,true)]
theorem der_31499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31499 :=
  CNF.rup_sound cl_31499 [cl_25707,cl_31498] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25707 v h) (hints_cons _ _ _ (der_31498 v h) (by intro d hd; cases hd)))
def cl_31501 : CNF.NClause := [(50,false),(60,false),(37,true),(41,true),(105,true)]
theorem der_31501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31501 :=
  CNF.rup_sound cl_31501 [cl_25709,cl_30760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25709 v h) (hints_cons _ _ _ (der_30760 v h) (by intro d hd; cases hd)))
def cl_31502 : CNF.NClause := [(41,false),(60,false),(37,false),(33,true),(105,true)]
theorem der_31502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31502 :=
  CNF.rup_sound cl_31502 [cl_25710,cl_31498] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25710 v h) (hints_cons _ _ _ (der_31498 v h) (by intro d hd; cases hd)))
def cl_31503 : CNF.NClause := [(41,false),(60,false),(50,true),(33,true),(105,true)]
theorem der_31503 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31503 :=
  CNF.rup_sound cl_31503 [cl_25711,cl_31502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25711 v h) (hints_cons _ _ _ (der_31502 v h) (by intro d hd; cases hd)))
def cl_31504 : CNF.NClause := [(60,false),(37,false),(54,true),(33,true),(105,true)]
theorem der_31504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31504 :=
  CNF.rup_sound cl_31504 [cl_25712,cl_31502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25712 v h) (hints_cons _ _ _ (der_31502 v h) (by intro d hd; cases hd)))
def cl_31505 : CNF.NClause := [(41,false),(50,false),(54,false),(37,false),(105,true)]
theorem der_31505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31505 :=
  CNF.rup_sound cl_31505 [cl_25713,cl_31498] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25713 v h) (hints_cons _ _ _ (der_31498 v h) (by intro d hd; cases hd)))
def cl_31506 : CNF.NClause := [(41,false),(50,false),(54,false),(37,true),(105,true)]
theorem der_31506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31506 :=
  CNF.rup_sound cl_31506 [cl_25714,cl_30767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25714 v h) (hints_cons _ _ _ (der_30767 v h) (by intro d hd; cases hd)))
def cl_31507 : CNF.NClause := [(50,false),(54,false),(37,false),(33,true),(105,true)]
theorem der_31507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31507 :=
  CNF.rup_sound cl_31507 [cl_25715,cl_31505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25715 v h) (hints_cons _ _ _ (der_31505 v h) (by intro d hd; cases hd)))
def cl_31508 : CNF.NClause := [(50,false),(54,false),(41,true),(33,true),(105,true)]
theorem der_31508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31508 :=
  CNF.rup_sound cl_31508 [cl_25716,cl_31507] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25716 v h) (hints_cons _ _ _ (der_31507 v h) (by intro d hd; cases hd)))
def cl_31509 : CNF.NClause := [(41,false),(54,false),(37,false),(33,true),(105,true)]
theorem der_31509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31509 :=
  CNF.rup_sound cl_31509 [cl_25717,cl_31507] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25717 v h) (hints_cons _ _ _ (der_31507 v h) (by intro d hd; cases hd)))
def cl_31510 : CNF.NClause := [(41,false),(54,false),(50,true),(33,true),(105,true)]
theorem der_31510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31510 :=
  CNF.rup_sound cl_31510 [cl_25718,cl_31509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25718 v h) (hints_cons _ _ _ (der_31509 v h) (by intro d hd; cases hd)))
def cl_31511 : CNF.NClause := [(54,false),(37,false),(60,true),(33,true),(105,true)]
theorem der_31511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31511 :=
  CNF.rup_sound cl_31511 [cl_25719,cl_31507] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25719 v h) (hints_cons _ _ _ (der_31507 v h) (by intro d hd; cases hd)))
def cl_31512 : CNF.NClause := [(41,false),(50,false),(37,false),(54,true),(105,true)]
theorem der_31512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31512 :=
  CNF.rup_sound cl_31512 [cl_25720,cl_31498] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25720 v h) (hints_cons _ _ _ (der_31498 v h) (by intro d hd; cases hd)))
def cl_31513 : CNF.NClause := [(41,false),(50,false),(37,true),(54,true),(105,true)]
theorem der_31513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31513 :=
  CNF.rup_sound cl_31513 [cl_25721,cl_31499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25721 v h) (hints_cons _ _ _ (der_31499 v h) (by intro d hd; cases hd)))
def cl_31514 : CNF.NClause := [(50,false),(37,false),(41,true),(33,true),(105,true)]
theorem der_31514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31514 :=
  CNF.rup_sound cl_31514 [cl_25722,cl_31507] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25722 v h) (hints_cons _ _ _ (der_31507 v h) (by intro d hd; cases hd)))
def cl_31515 : CNF.NClause := [(41,false),(37,false),(50,true),(33,true),(105,true)]
theorem der_31515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31515 :=
  CNF.rup_sound cl_31515 [cl_25723,cl_31509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25723 v h) (hints_cons _ _ _ (der_31509 v h) (by intro d hd; cases hd)))
def cl_31518 : CNF.NClause := [(57,false),(39,false),(52,false),(33,true),(110,true)]
theorem der_31518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31518 :=
  CNF.rup_sound cl_31518 [cl_25729,cl_25727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25729 v h) (hints_cons _ _ _ (der_25727 v h) (by intro d hd; cases hd)))
def cl_31519 : CNF.NClause := [(57,false),(52,false),(45,true),(39,true),(110,true)]
theorem der_31519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31519 :=
  CNF.rup_sound cl_31519 [cl_25730,cl_30725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25730 v h) (hints_cons _ _ _ (der_30725 v h) (by intro d hd; cases hd)))
def cl_31520 : CNF.NClause := [(57,false),(39,false),(46,false),(52,true),(110,true)]
theorem der_31520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31520 :=
  CNF.rup_sound cl_31520 [cl_25733,cl_25731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25733 v h) (hints_cons _ _ _ (der_25731 v h) (by intro d hd; cases hd)))
def cl_31521 : CNF.NClause := [(57,false),(46,false),(39,true),(33,true),(110,true)]
theorem der_31521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31521 :=
  CNF.rup_sound cl_31521 [cl_25734,cl_25732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25734 v h) (hints_cons _ _ _ (der_25732 v h) (by intro d hd; cases hd)))
def cl_31522 : CNF.NClause := [(57,false),(39,false),(45,false),(52,true),(110,true)]
theorem der_31522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31522 :=
  CNF.rup_sound cl_31522 [cl_25735,cl_31520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25735 v h) (hints_cons _ _ _ (der_31520 v h) (by intro d hd; cases hd)))
def cl_31523 : CNF.NClause := [(57,false),(45,false),(46,true),(52,true),(110,true)]
theorem der_31523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31523 :=
  CNF.rup_sound cl_31523 [cl_25736,cl_31522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25736 v h) (hints_cons _ _ _ (der_31522 v h) (by intro d hd; cases hd)))
def cl_31524 : CNF.NClause := [(57,false),(39,false),(46,true),(52,true),(110,true)]
theorem der_31524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31524 :=
  CNF.rup_sound cl_31524 [cl_25737,cl_31522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25737 v h) (hints_cons _ _ _ (der_31522 v h) (by intro d hd; cases hd)))
def cl_31525 : CNF.NClause := [(46,false),(45,false),(52,false),(39,true),(110,true)]
theorem der_31525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31525 :=
  CNF.rup_sound cl_31525 [cl_25739,cl_30729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25739 v h) (hints_cons _ _ _ (der_30729 v h) (by intro d hd; cases hd)))
def cl_31526 : CNF.NClause := [(39,false),(46,false),(52,false),(33,true),(110,true)]
theorem der_31526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31526 :=
  CNF.rup_sound cl_31526 [cl_25740,cl_25738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25740 v h) (hints_cons _ _ _ (der_25738 v h) (by intro d hd; cases hd)))
def cl_31527 : CNF.NClause := [(46,false),(52,false),(45,true),(39,true),(110,true)]
theorem der_31527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31527 :=
  CNF.rup_sound cl_31527 [cl_25741,cl_31519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25741 v h) (hints_cons _ _ _ (der_31519 v h) (by intro d hd; cases hd)))
def cl_31528 : CNF.NClause := [(39,false),(45,false),(52,false),(33,true),(110,true)]
theorem der_31528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31528 :=
  CNF.rup_sound cl_31528 [cl_25742,cl_25738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25742 v h) (hints_cons _ _ _ (der_25738 v h) (by intro d hd; cases hd)))
def cl_31529 : CNF.NClause := [(45,false),(52,false),(39,true),(46,true),(110,true)]
theorem der_31529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31529 :=
  CNF.rup_sound cl_31529 [cl_25743,cl_30729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25743 v h) (hints_cons _ _ _ (der_30729 v h) (by intro d hd; cases hd)))
def cl_31530 : CNF.NClause := [(39,false),(52,false),(33,true),(57,true),(110,true)]
theorem der_31530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31530 :=
  CNF.rup_sound cl_31530 [cl_25744,cl_31528] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25744 v h) (hints_cons _ _ _ (der_31528 v h) (by intro d hd; cases hd)))
def cl_31531 : CNF.NClause := [(39,false),(46,false),(45,false),(33,true),(110,true)]
theorem der_31531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31531 :=
  CNF.rup_sound cl_31531 [cl_25745,cl_31528] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25745 v h) (hints_cons _ _ _ (der_31528 v h) (by intro d hd; cases hd)))
def cl_31532 : CNF.NClause := [(46,false),(45,false),(39,true),(57,true),(110,true)]
theorem der_31532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31532 :=
  CNF.rup_sound cl_31532 [cl_25746,cl_24719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25746 v h) (hints_cons _ _ _ (der_24719 v h) (by intro d hd; cases hd)))
def cl_31533 : CNF.NClause := [(39,false),(46,false),(52,true),(33,true),(110,true)]
theorem der_31533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31533 :=
  CNF.rup_sound cl_31533 [cl_25747,cl_31520] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25747 v h) (hints_cons _ _ _ (der_31520 v h) (by intro d hd; cases hd)))
def cl_31534 : CNF.NClause := [(39,false),(45,false),(33,true),(57,true),(110,true)]
theorem der_31534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31534 :=
  CNF.rup_sound cl_31534 [cl_25748,cl_31531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25748 v h) (hints_cons _ _ _ (der_31531 v h) (by intro d hd; cases hd)))
def cl_31536 : CNF.NClause := [(59,false),(55,false),(44,false),(36,true),(115,true)]
theorem der_31536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31536 :=
  CNF.rup_sound cl_31536 [cl_25754,cl_25750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25754 v h) (hints_cons _ _ _ (der_25750 v h) (by intro d hd; cases hd)))
def cl_31537 : CNF.NClause := [(59,false),(36,false),(55,false),(44,true),(115,true)]
theorem der_31537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31537 :=
  CNF.rup_sound cl_31537 [cl_25755,cl_25751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25755 v h) (hints_cons _ _ _ (der_25751 v h) (by intro d hd; cases hd)))
def cl_31538 : CNF.NClause := [(59,false),(55,false),(47,true),(36,true),(115,true)]
theorem der_31538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31538 :=
  CNF.rup_sound cl_31538 [cl_25756,cl_31536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25756 v h) (hints_cons _ _ _ (der_31536 v h) (by intro d hd; cases hd)))
def cl_31539 : CNF.NClause := [(59,false),(47,false),(44,false),(36,true),(115,true)]
theorem der_31539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31539 :=
  CNF.rup_sound cl_31539 [cl_25758,cl_24870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25758 v h) (hints_cons _ _ _ (der_24870 v h) (by intro d hd; cases hd)))
def cl_31540 : CNF.NClause := [(59,false),(36,false),(47,false),(55,true),(115,true)]
theorem der_31540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31540 :=
  CNF.rup_sound cl_31540 [cl_25759,cl_25757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25759 v h) (hints_cons _ _ _ (der_25757 v h) (by intro d hd; cases hd)))
def cl_31541 : CNF.NClause := [(59,false),(47,false),(44,true),(36,true),(115,true)]
theorem der_31541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31541 :=
  CNF.rup_sound cl_31541 [cl_25760,cl_30838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25760 v h) (hints_cons _ _ _ (der_30838 v h) (by intro d hd; cases hd)))
def cl_31542 : CNF.NClause := [(59,false),(36,false),(44,false),(55,true),(115,true)]
theorem der_31542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31542 :=
  CNF.rup_sound cl_31542 [cl_25761,cl_25757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25761 v h) (hints_cons _ _ _ (der_25757 v h) (by intro d hd; cases hd)))
def cl_31543 : CNF.NClause := [(59,false),(44,false),(47,true),(36,true),(115,true)]
theorem der_31543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31543 :=
  CNF.rup_sound cl_31543 [cl_25762,cl_31538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25762 v h) (hints_cons _ _ _ (der_31538 v h) (by intro d hd; cases hd)))
def cl_31544 : CNF.NClause := [(59,false),(36,false),(47,true),(55,true),(115,true)]
theorem der_31544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31544 :=
  CNF.rup_sound cl_31544 [cl_25763,cl_31542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25763 v h) (hints_cons _ _ _ (der_31542 v h) (by intro d hd; cases hd)))
def cl_31545 : CNF.NClause := [(55,false),(47,false),(44,false),(36,true),(115,true)]
theorem der_31545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31545 :=
  CNF.rup_sound cl_31545 [cl_25765,cl_30841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25765 v h) (hints_cons _ _ _ (der_30841 v h) (by intro d hd; cases hd)))
def cl_31546 : CNF.NClause := [(36,false),(55,false),(47,false),(44,true),(115,true)]
theorem der_31546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31546 :=
  CNF.rup_sound cl_31546 [cl_25766,cl_31537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25766 v h) (hints_cons _ _ _ (der_31537 v h) (by intro d hd; cases hd)))
def cl_31547 : CNF.NClause := [(55,false),(47,false),(36,true),(33,true),(115,true)]
theorem der_31547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31547 :=
  CNF.rup_sound cl_31547 [cl_25767,cl_31545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25767 v h) (hints_cons _ _ _ (der_31545 v h) (by intro d hd; cases hd)))
def cl_31548 : CNF.NClause := [(36,false),(55,false),(44,false),(33,true),(115,true)]
theorem der_31548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31548 :=
  CNF.rup_sound cl_31548 [cl_25768,cl_25764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25768 v h) (hints_cons _ _ _ (der_25764 v h) (by intro d hd; cases hd)))
def cl_31549 : CNF.NClause := [(55,false),(44,false),(47,true),(36,true),(115,true)]
theorem der_31549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31549 :=
  CNF.rup_sound cl_31549 [cl_25769,cl_31536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25769 v h) (hints_cons _ _ _ (der_31536 v h) (by intro d hd; cases hd)))
def cl_31550 : CNF.NClause := [(36,false),(55,false),(44,true),(33,true),(115,true)]
theorem der_31550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31550 :=
  CNF.rup_sound cl_31550 [cl_25770,cl_31546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25770 v h) (hints_cons _ _ _ (der_31546 v h) (by intro d hd; cases hd)))
def cl_31551 : CNF.NClause := [(36,false),(47,false),(44,false),(55,true),(115,true)]
theorem der_31551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31551 :=
  CNF.rup_sound cl_31551 [cl_25771,cl_31542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25771 v h) (hints_cons _ _ _ (der_31542 v h) (by intro d hd; cases hd)))
def cl_31552 : CNF.NClause := [(36,false),(47,false),(44,true),(59,true),(115,true)]
theorem der_31552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31552 :=
  CNF.rup_sound cl_31552 [cl_25773,cl_30115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25773 v h) (hints_cons _ _ _ (der_30115 v h) (by intro d hd; cases hd)))
def cl_31553 : CNF.NClause := [(36,false),(44,false),(47,true),(55,true),(115,true)]
theorem der_31553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31553 :=
  CNF.rup_sound cl_31553 [cl_25774,cl_31542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25774 v h) (hints_cons _ _ _ (der_31542 v h) (by intro d hd; cases hd)))
def cl_31554 : CNF.NClause := [(32,false),(34,false),(33,true),(35,true),(118,true)]
theorem der_31554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31554 :=
  CNF.rup_sound cl_31554 [cl_25775,cl_31003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25775 v h) (hints_cons _ _ _ (der_31003 v h) (by intro d hd; cases hd)))
def cl_31555 : CNF.NClause := [(57,false),(61,false),(60,false),(56,true),(93,true)]
theorem der_31555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31555 :=
  CNF.rup_sound cl_31555 [cl_25777,cl_31353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25777 v h) (hints_cons _ _ _ (der_31353 v h) (by intro d hd; cases hd)))
def cl_31556 : CNF.NClause := [(57,false),(61,false),(58,false),(60,true),(93,true)]
theorem der_31556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31556 :=
  CNF.rup_sound cl_31556 [cl_25778,cl_31362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25778 v h) (hints_cons _ _ _ (der_31362 v h) (by intro d hd; cases hd)))
def cl_31558 : CNF.NClause := [(51,false),(48,false),(34,false),(45,true),(101,true)]
theorem der_31558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31558 :=
  CNF.rup_sound cl_31558 [cl_25780,cl_30792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25780 v h) (hints_cons _ _ _ (der_30792 v h) (by intro d hd; cases hd)))
def cl_31559 : CNF.NClause := [(36,false),(33,false),(47,false),(59,true),(115,true)]
theorem der_31559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31559 :=
  CNF.rup_sound cl_31559 [cl_25781,cl_31146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25781 v h) (hints_cons _ _ _ (der_31146 v h) (by intro d hd; cases hd)))
def cl_31560 : CNF.NClause := [(32,false),(40,false),(54,false),(46,false),(112,true)]
theorem der_31560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31560 :=
  CNF.rup_sound cl_31560 [cl_25782,cl_25610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25782 v h) (hints_cons _ _ _ (der_25610 v h) (by intro d hd; cases hd)))
def cl_31561 : CNF.NClause := [(57,false),(60,false),(58,false),(61,true),(93,true)]
theorem der_31561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31561 :=
  CNF.rup_sound cl_31561 [cl_25783,cl_31370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25783 v h) (hints_cons _ _ _ (der_31370 v h) (by intro d hd; cases hd)))
def cl_31562 : CNF.NClause := [(57,false),(58,false),(60,true),(61,true),(93,true)]
theorem der_31562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31562 :=
  CNF.rup_sound cl_31562 [cl_25784,cl_31378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25784 v h) (hints_cons _ _ _ (der_31378 v h) (by intro d hd; cases hd)))
def cl_31564 : CNF.NClause := [(50,false),(42,false),(31,true),(59,true),(121,true)]
theorem der_31564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31564 :=
  CNF.rup_sound cl_31564 [cl_25786,cl_30064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25786 v h) (hints_cons _ _ _ (der_30064 v h) (by intro d hd; cases hd)))
def cl_31565 : CNF.NClause := [(32,false),(54,false),(46,false),(40,true),(112,true)]
theorem der_31565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31565 :=
  CNF.rup_sound cl_31565 [cl_25788,cl_31442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25788 v h) (hints_cons _ _ _ (der_31442 v h) (by intro d hd; cases hd)))
def cl_31567 : CNF.NClause := [(36,false),(115,true),(44,false),(59,true),(33,false)]
theorem der_31567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31567 :=
  CNF.rup_sound cl_31567 [cl_25790,cl_31559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25790 v h) (hints_cons _ _ _ (der_31559 v h) (by intro d hd; cases hd)))
def cl_31568 : CNF.NClause := [(51,false),(45,false),(34,false),(59,true),(101,true)]
theorem der_31568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31568 :=
  CNF.rup_sound cl_31568 [cl_25791,cl_30793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25791 v h) (hints_cons _ _ _ (der_30793 v h) (by intro d hd; cases hd)))
def cl_31569 : CNF.NClause := [(51,false),(34,false),(45,true),(48,true),(101,true)]
theorem der_31569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31569 :=
  CNF.rup_sound cl_31569 [cl_25792,cl_30794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25792 v h) (hints_cons _ _ _ (der_30794 v h) (by intro d hd; cases hd)))
def cl_31570 : CNF.NClause := [(42,false),(39,false),(53,false),(59,true),(121,true)]
theorem der_31570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31570 :=
  CNF.rup_sound cl_31570 [cl_25793,cl_31075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25793 v h) (hints_cons _ _ _ (der_31075 v h) (by intro d hd; cases hd)))
def cl_31571 : CNF.NClause := [(42,false),(53,false),(39,true),(59,true),(121,true)]
theorem der_31571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31571 :=
  CNF.rup_sound cl_31571 [cl_25794,cl_31076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25794 v h) (hints_cons _ _ _ (der_31076 v h) (by intro d hd; cases hd)))
def cl_31572 : CNF.NClause := [(32,false),(54,false),(43,false),(40,true),(112,true)]
theorem der_31572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31572 :=
  CNF.rup_sound cl_31572 [cl_25795,cl_31565] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25795 v h) (hints_cons _ _ _ (der_31565 v h) (by intro d hd; cases hd)))
def cl_31573 : CNF.NClause := [(36,false),(55,false),(47,true),(44,true),(115,true)]
theorem der_31573 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31573 :=
  CNF.rup_sound cl_31573 [cl_25796,cl_31550] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25796 v h) (hints_cons _ _ _ (der_31550 v h) (by intro d hd; cases hd)))
def cl_31574 : CNF.NClause := [(57,false),(45,false),(33,false),(46,true),(110,true)]
theorem der_31574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31574 :=
  CNF.rup_sound cl_31574 [cl_25797,cl_31523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25797 v h) (hints_cons _ _ _ (der_31523 v h) (by intro d hd; cases hd)))
def cl_31575 : CNF.NClause := [(57,false),(39,false),(33,false),(46,true),(110,true)]
theorem der_31575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31575 :=
  CNF.rup_sound cl_31575 [cl_25800,cl_31574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25800 v h) (hints_cons _ _ _ (der_31574 v h) (by intro d hd; cases hd)))
def cl_31577 : CNF.NClause := [(58,false),(34,false),(52,false),(50,true),(116,true)]
theorem der_31577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31577 :=
  CNF.rup_sound cl_31577 [cl_25804,cl_31422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25804 v h) (hints_cons _ _ _ (der_31422 v h) (by intro d hd; cases hd)))
def cl_31578 : CNF.NClause := [(58,true),(52,false),(43,false),(50,true),(116,true)]
theorem der_31578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31578 :=
  CNF.rup_sound cl_31578 [cl_25805,cl_31320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25805 v h) (hints_cons _ _ _ (der_31320 v h) (by intro d hd; cases hd)))
def cl_31579 : CNF.NClause := [(51,false),(54,false),(55,false),(61,true),(98,true)]
theorem der_31579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31579 :=
  CNF.rup_sound cl_31579 [cl_25806,cl_30096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25806 v h) (hints_cons _ _ _ (der_30096 v h) (by intro d hd; cases hd)))
def cl_31580 : CNF.NClause := [(32,false),(42,false),(37,false),(56,true),(97,true)]
theorem der_31580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31580 :=
  CNF.rup_sound cl_31580 [cl_25807,cl_25798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25807 v h) (hints_cons _ _ _ (der_25798 v h) (by intro d hd; cases hd)))
def cl_31581 : CNF.NClause := [(60,false),(52,false),(44,false),(48,true),(119,true)]
theorem der_31581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31581 :=
  CNF.rup_sound cl_31581 [cl_25811,cl_31009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25811 v h) (hints_cons _ _ _ (der_31009 v h) (by intro d hd; cases hd)))
def cl_31582 : CNF.NClause := [(60,false),(40,false),(31,true),(44,true),(119,true)]
theorem der_31582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31582 :=
  CNF.rup_sound cl_31582 [cl_25812,cl_25810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25812 v h) (hints_cons _ _ _ (der_25810 v h) (by intro d hd; cases hd)))
def cl_31583 : CNF.NClause := [(50,false),(34,false),(36,false),(43,false),(116,true)]
theorem der_31583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31583 :=
  CNF.rup_sound cl_31583 [cl_25814,cl_25049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25814 v h) (hints_cons _ _ _ (der_25049 v h) (by intro d hd; cases hd)))
def cl_31584 : CNF.NClause := [(60,false),(52,false),(40,true),(48,true),(119,true)]
theorem der_31584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31584 :=
  CNF.rup_sound cl_31584 [cl_25815,cl_25802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25815 v h) (hints_cons _ _ _ (der_25802 v h) (by intro d hd; cases hd)))
def cl_31585 : CNF.NClause := [(41,false),(35,false),(59,false),(49,true),(104,true)]
theorem der_31585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31585 :=
  CNF.rup_sound cl_31585 [cl_25817,cl_30104] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25817 v h) (hints_cons _ _ _ (der_30104 v h) (by intro d hd; cases hd)))
def cl_31586 : CNF.NClause := [(41,false),(35,false),(38,false),(59,true),(104,true)]
theorem der_31586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31586 :=
  CNF.rup_sound cl_31586 [cl_25819,cl_25818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25819 v h) (hints_cons _ _ _ (der_25818 v h) (by intro d hd; cases hd)))
def cl_31589 : CNF.NClause := [(50,false),(49,false),(47,true),(46,true),(108,true)]
theorem der_31589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31589 :=
  CNF.rup_sound cl_31589 [cl_25822,cl_31165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25822 v h) (hints_cons _ _ _ (der_31165 v h) (by intro d hd; cases hd)))
def cl_31590 : CNF.NClause := [(48,false),(50,false),(46,false),(47,true),(108,true)]
theorem der_31590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31590 :=
  CNF.rup_sound cl_31590 [cl_25823,cl_30114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25823 v h) (hints_cons _ _ _ (der_30114 v h) (by intro d hd; cases hd)))
def cl_31591 : CNF.NClause := [(32,false),(60,false),(36,false),(53,true),(117,true)]
theorem der_31591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31591 :=
  CNF.rup_sound cl_31591 [cl_25825,cl_23754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25825 v h) (hints_cons _ _ _ (der_23754 v h) (by intro d hd; cases hd)))
def cl_31592 : CNF.NClause := [(32,false),(36,false),(49,false),(53,true),(117,true)]
theorem der_31592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31592 :=
  CNF.rup_sound cl_31592 [cl_25826,cl_23740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25826 v h) (hints_cons _ _ _ (der_23740 v h) (by intro d hd; cases hd)))
def cl_31593 : CNF.NClause := [(51,false),(42,false),(58,false),(40,false),(100,true)]
theorem der_31593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31593 :=
  CNF.rup_sound cl_31593 [cl_25827,cl_31481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25827 v h) (hints_cons _ _ _ (der_31481 v h) (by intro d hd; cases hd)))
def cl_31594 : CNF.NClause := [(51,false),(42,false),(33,false),(58,false),(100,true)]
theorem der_31594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31594 :=
  CNF.rup_sound cl_31594 [cl_25828,cl_31593] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25828 v h) (hints_cons _ _ _ (der_31593 v h) (by intro d hd; cases hd)))
def cl_31595 : CNF.NClause := [(32,false),(53,false),(49,false),(45,true),(117,true)]
theorem der_31595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31595 :=
  CNF.rup_sound cl_31595 [cl_25829,cl_30848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25829 v h) (hints_cons _ _ _ (der_30848 v h) (by intro d hd; cases hd)))
def cl_31597 : CNF.NClause := [(32,false),(36,false),(45,false),(60,true),(117,true)]
theorem der_31597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31597 :=
  CNF.rup_sound cl_31597 [cl_25831,cl_30069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25831 v h) (hints_cons _ _ _ (der_30069 v h) (by intro d hd; cases hd)))
def cl_31599 : CNF.NClause := [(39,false),(54,false),(44,true),(56,true),(96,true)]
theorem der_31599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31599 :=
  CNF.rup_sound cl_31599 [cl_25834,cl_31233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25834 v h) (hints_cons _ _ _ (der_31233 v h) (by intro d hd; cases hd)))
def cl_31600 : CNF.NClause := [(39,false),(34,false),(56,true),(54,true),(96,true)]
theorem der_31600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31600 :=
  CNF.rup_sound cl_31600 [cl_25835,cl_31384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25835 v h) (hints_cons _ _ _ (der_31384 v h) (by intro d hd; cases hd)))
def cl_31603 : CNF.NClause := [(39,false),(34,false),(44,true),(54,true),(96,true)]
theorem der_31603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31603 :=
  CNF.rup_sound cl_31603 [cl_25838,cl_30117] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25838 v h) (hints_cons _ _ _ (der_30117 v h) (by intro d hd; cases hd)))
def cl_31605 : CNF.NClause := [(34,false),(49,false),(39,true),(56,true),(96,true)]
theorem der_31605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31605 :=
  CNF.rup_sound cl_31605 [cl_25840,cl_24754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25840 v h) (hints_cons _ _ _ (der_24754 v h) (by intro d hd; cases hd)))
def cl_31606 : CNF.NClause := [(41,false),(35,false),(38,false),(52,true),(104,true)]
theorem der_31606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31606 :=
  CNF.rup_sound cl_31606 [cl_25842,cl_31586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25842 v h) (hints_cons _ _ _ (der_31586 v h) (by intro d hd; cases hd)))
def cl_31609 : CNF.NClause := [(61,false),(42,false),(45,false),(44,false),(103,true)]
theorem der_31609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31609 :=
  CNF.rup_sound cl_31609 [cl_25846,cl_25844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25846 v h) (hints_cons _ _ _ (der_25844 v h) (by intro d hd; cases hd)))
def cl_31610 : CNF.NClause := [(61,false),(45,false),(44,false),(43,true),(103,true)]
theorem der_31610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31610 :=
  CNF.rup_sound cl_31610 [cl_25847,cl_31609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25847 v h) (hints_cons _ _ _ (der_31609 v h) (by intro d hd; cases hd)))
def cl_31611 : CNF.NClause := [(61,false),(42,false),(43,false),(45,false),(103,true)]
theorem der_31611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31611 :=
  CNF.rup_sound cl_31611 [cl_25848,cl_31609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25848 v h) (hints_cons _ _ _ (der_31609 v h) (by intro d hd; cases hd)))
def cl_31612 : CNF.NClause := [(61,false),(45,false),(43,false),(41,true),(103,true)]
theorem der_31612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31612 :=
  CNF.rup_sound cl_31612 [cl_25849,cl_31611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25849 v h) (hints_cons _ _ _ (der_31611 v h) (by intro d hd; cases hd)))
def cl_31613 : CNF.NClause := [(61,false),(42,false),(45,false),(43,true),(103,true)]
theorem der_31613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31613 :=
  CNF.rup_sound cl_31613 [cl_25850,cl_31609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25850 v h) (hints_cons _ _ _ (der_31609 v h) (by intro d hd; cases hd)))
def cl_31614 : CNF.NClause := [(61,false),(45,false),(44,true),(43,true),(103,true)]
theorem der_31614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31614 :=
  CNF.rup_sound cl_31614 [cl_25851,cl_31613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25851 v h) (hints_cons _ _ _ (der_31613 v h) (by intro d hd; cases hd)))
def cl_31615 : CNF.NClause := [(61,false),(42,false),(43,false),(44,false),(103,true)]
theorem der_31615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31615 :=
  CNF.rup_sound cl_31615 [cl_25852,cl_31609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25852 v h) (hints_cons _ _ _ (der_31609 v h) (by intro d hd; cases hd)))
def cl_31619 : CNF.NClause := [(61,false),(42,false),(43,false),(45,true),(103,true)]
theorem der_31619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31619 :=
  CNF.rup_sound cl_31619 [cl_25856,cl_31615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25856 v h) (hints_cons _ _ _ (der_31615 v h) (by intro d hd; cases hd)))
def cl_31622 : CNF.NClause := [(45,false),(103,true),(44,false),(41,true),(43,false)]
theorem der_31622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31622 :=
  CNF.rup_sound cl_31622 [cl_25860,cl_25859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25860 v h) (hints_cons _ _ _ (der_25859 v h) (by intro d hd; cases hd)))
def cl_31623 : CNF.NClause := [(42,false),(45,false),(44,false),(43,true),(103,true)]
theorem der_31623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31623 :=
  CNF.rup_sound cl_31623 [cl_25861,cl_31610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25861 v h) (hints_cons _ _ _ (der_31610 v h) (by intro d hd; cases hd)))
def cl_31624 : CNF.NClause := [(42,false),(103,true),(45,false),(41,true),(43,false)]
theorem der_31624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31624 :=
  CNF.rup_sound cl_31624 [cl_25863,cl_31611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25863 v h) (hints_cons _ _ _ (der_31611 v h) (by intro d hd; cases hd)))
def cl_31625 : CNF.NClause := [(45,false),(42,true),(43,false),(41,true),(103,true)]
theorem der_31625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31625 :=
  CNF.rup_sound cl_31625 [cl_25864,cl_31612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25864 v h) (hints_cons _ _ _ (der_31612 v h) (by intro d hd; cases hd)))
def cl_31626 : CNF.NClause := [(42,false),(45,false),(44,true),(43,true),(103,true)]
theorem der_31626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31626 :=
  CNF.rup_sound cl_31626 [cl_25865,cl_31614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25865 v h) (hints_cons _ _ _ (der_31614 v h) (by intro d hd; cases hd)))
def cl_31627 : CNF.NClause := [(42,false),(44,false),(41,true),(43,false),(103,true)]
theorem der_31627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31627 :=
  CNF.rup_sound cl_31627 [cl_25866,cl_31615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25866 v h) (hints_cons _ _ _ (der_31615 v h) (by intro d hd; cases hd)))
def cl_31628 : CNF.NClause := [(44,false),(42,true),(43,false),(61,true),(103,true)]
theorem der_31628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31628 :=
  CNF.rup_sound cl_31628 [cl_25867,cl_31208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25867 v h) (hints_cons _ _ _ (der_31208 v h) (by intro d hd; cases hd)))
def cl_31629 : CNF.NClause := [(42,false),(44,false),(43,true),(41,true),(103,true)]
theorem der_31629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31629 :=
  CNF.rup_sound cl_31629 [cl_25868,cl_31623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25868 v h) (hints_cons _ _ _ (der_31623 v h) (by intro d hd; cases hd)))
def cl_31630 : CNF.NClause := [(42,false),(44,true),(45,true),(43,false),(103,true)]
theorem der_31630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31630 :=
  CNF.rup_sound cl_31630 [cl_25869,cl_31619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25869 v h) (hints_cons _ _ _ (der_31619 v h) (by intro d hd; cases hd)))
def cl_31633 : CNF.NClause := [(36,false),(46,false),(56,false),(41,true),(123,true)]
theorem der_31633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31633 :=
  CNF.rup_sound cl_31633 [cl_25872,cl_31112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25872 v h) (hints_cons _ _ _ (der_31112 v h) (by intro d hd; cases hd)))
def cl_31634 : CNF.NClause := [(36,false),(56,false),(31,true),(41,true),(123,true)]
theorem der_31634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31634 :=
  CNF.rup_sound cl_31634 [cl_25873,cl_31633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25873 v h) (hints_cons _ _ _ (der_31633 v h) (by intro d hd; cases hd)))
def cl_31635 : CNF.NClause := [(32,false),(48,false),(58,false),(55,false),(107,true)]
theorem der_31635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31635 :=
  CNF.rup_sound cl_31635 [cl_25874,cl_30735] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25874 v h) (hints_cons _ _ _ (der_30735 v h) (by intro d hd; cases hd)))
def cl_31636 : CNF.NClause := [(32,false),(58,false),(55,false),(48,true),(107,true)]
theorem der_31636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31636 :=
  CNF.rup_sound cl_31636 [cl_25875,cl_30734] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25875 v h) (hints_cons _ _ _ (der_30734 v h) (by intro d hd; cases hd)))
def cl_31637 : CNF.NClause := [(32,false),(48,false),(58,false),(55,true),(107,true)]
theorem der_31637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31637 :=
  CNF.rup_sound cl_31637 [cl_25876,cl_30735] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25876 v h) (hints_cons _ _ _ (der_30735 v h) (by intro d hd; cases hd)))
def cl_31638 : CNF.NClause := [(32,false),(39,false),(58,false),(48,true),(107,true)]
theorem der_31638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31638 :=
  CNF.rup_sound cl_31638 [cl_25877,cl_31636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25877 v h) (hints_cons _ _ _ (der_31636 v h) (by intro d hd; cases hd)))
def cl_31639 : CNF.NClause := [(32,false),(48,false),(55,false),(58,true),(107,true)]
theorem der_31639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31639 :=
  CNF.rup_sound cl_31639 [cl_25878,cl_30742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25878 v h) (hints_cons _ _ _ (der_30742 v h) (by intro d hd; cases hd)))
def cl_31640 : CNF.NClause := [(32,false),(39,false),(55,false),(58,true),(107,true)]
theorem der_31640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31640 :=
  CNF.rup_sound cl_31640 [cl_25879,cl_31639] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25879 v h) (hints_cons _ _ _ (der_31639 v h) (by intro d hd; cases hd)))
def cl_31642 : CNF.NClause := [(32,false),(39,false),(48,true),(58,true),(107,true)]
theorem der_31642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31642 :=
  CNF.rup_sound cl_31642 [cl_25881,cl_31640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25881 v h) (hints_cons _ _ _ (der_31640 v h) (by intro d hd; cases hd)))
def cl_31643 : CNF.NClause := [(50,false),(60,false),(33,false),(54,false),(105,true)]
theorem der_31643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31643 :=
  CNF.rup_sound cl_31643 [cl_25882,cl_30760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25882 v h) (hints_cons _ _ _ (der_30760 v h) (by intro d hd; cases hd)))
def cl_31644 : CNF.NClause := [(60,false),(54,false),(41,true),(33,false),(105,true)]
theorem der_31644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31644 :=
  CNF.rup_sound cl_31644 [cl_25883,cl_31643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25883 v h) (hints_cons _ _ _ (der_31643 v h) (by intro d hd; cases hd)))
def cl_31645 : CNF.NClause := [(50,false),(60,false),(33,false),(54,true),(105,true)]
theorem der_31645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31645 :=
  CNF.rup_sound cl_31645 [cl_25884,cl_31499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25884 v h) (hints_cons _ _ _ (der_31499 v h) (by intro d hd; cases hd)))
def cl_31646 : CNF.NClause := [(60,false),(54,true),(41,true),(33,false),(105,true)]
theorem der_31646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31646 :=
  CNF.rup_sound cl_31646 [cl_25885,cl_31645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25885 v h) (hints_cons _ _ _ (der_31645 v h) (by intro d hd; cases hd)))
def cl_31647 : CNF.NClause := [(50,false),(54,false),(37,false),(60,true),(105,true)]
theorem der_31647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31647 :=
  CNF.rup_sound cl_31647 [cl_25886,cl_31507] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25886 v h) (hints_cons _ _ _ (der_31507 v h) (by intro d hd; cases hd)))
def cl_31648 : CNF.NClause := [(54,false),(37,false),(60,true),(41,true),(105,true)]
theorem der_31648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31648 :=
  CNF.rup_sound cl_31648 [cl_25887,cl_31647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25887 v h) (hints_cons _ _ _ (der_31647 v h) (by intro d hd; cases hd)))
def cl_31649 : CNF.NClause := [(50,false),(105,true),(37,false),(54,true),(33,false)]
theorem der_31649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31649 :=
  CNF.rup_sound cl_31649 [cl_25888,cl_31645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25888 v h) (hints_cons _ _ _ (der_31645 v h) (by intro d hd; cases hd)))
def cl_31650 : CNF.NClause := [(37,false),(54,true),(41,true),(33,false),(105,true)]
theorem der_31650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31650 :=
  CNF.rup_sound cl_31650 [cl_25889,cl_31649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25889 v h) (hints_cons _ _ _ (der_31649 v h) (by intro d hd; cases hd)))
def cl_31651 : CNF.NClause := [(51,false),(46,false),(31,true),(56,true),(123,true)]
theorem der_31651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31651 :=
  CNF.rup_sound cl_31651 [cl_25890,cl_31383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25890 v h) (hints_cons _ _ _ (der_31383 v h) (by intro d hd; cases hd)))
def cl_31652 : CNF.NClause := [(51,false),(36,false),(31,true),(56,true),(123,true)]
theorem der_31652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31652 :=
  CNF.rup_sound cl_31652 [cl_25891,cl_31651] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25891 v h) (hints_cons _ _ _ (der_31651 v h) (by intro d hd; cases hd)))
def cl_31653 : CNF.NClause := [(36,false),(46,false),(41,true),(51,true),(123,true)]
theorem der_31653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31653 :=
  CNF.rup_sound cl_31653 [cl_25892,cl_31126] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25892 v h) (hints_cons _ _ _ (der_31126 v h) (by intro d hd; cases hd)))
def cl_31655 : CNF.NClause := [(57,false),(47,false),(53,false),(40,true),(106,true)]
theorem der_31655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31655 :=
  CNF.rup_sound cl_31655 [cl_25894,cl_31259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25894 v h) (hints_cons _ _ _ (der_31259 v h) (by intro d hd; cases hd)))
def cl_31657 : CNF.NClause := [(57,false),(106,true),(40,true),(41,true),(53,false)]
theorem der_31657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31657 :=
  CNF.rup_sound cl_31657 [cl_25896,cl_31655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25896 v h) (hints_cons _ _ _ (der_31655 v h) (by intro d hd; cases hd)))
def cl_31658 : CNF.NClause := [(57,false),(40,false),(47,false),(53,true),(106,true)]
theorem der_31658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31658 :=
  CNF.rup_sound cl_31658 [cl_25897,cl_31267] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25897 v h) (hints_cons _ _ _ (der_31267 v h) (by intro d hd; cases hd)))
def cl_31660 : CNF.NClause := [(57,false),(40,false),(34,false),(53,true),(106,true)]
theorem der_31660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31660 :=
  CNF.rup_sound cl_31660 [cl_25899,cl_31658] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25899 v h) (hints_cons _ _ _ (der_31658 v h) (by intro d hd; cases hd)))
def cl_31661 : CNF.NClause := [(57,false),(34,false),(40,true),(53,true),(106,true)]
theorem der_31661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31661 :=
  CNF.rup_sound cl_31661 [cl_25900,cl_30067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25900 v h) (hints_cons _ _ _ (der_30067 v h) (by intro d hd; cases hd)))
def cl_31662 : CNF.NClause := [(40,false),(47,false),(53,false),(41,true),(106,true)]
theorem der_31662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31662 :=
  CNF.rup_sound cl_31662 [cl_25901,cl_31273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25901 v h) (hints_cons _ _ _ (der_31273 v h) (by intro d hd; cases hd)))
def cl_31664 : CNF.NClause := [(40,false),(53,false),(47,true),(41,true),(106,true)]
theorem der_31664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31664 :=
  CNF.rup_sound cl_31664 [cl_25903,cl_31277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25903 v h) (hints_cons _ _ _ (der_31277 v h) (by intro d hd; cases hd)))
def cl_31665 : CNF.NClause := [(34,false),(106,true),(40,true),(41,true),(53,false)]
theorem der_31665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31665 :=
  CNF.rup_sound cl_31665 [cl_25904,cl_31657] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25904 v h) (hints_cons _ _ _ (der_31657 v h) (by intro d hd; cases hd)))
def cl_31666 : CNF.NClause := [(40,false),(47,false),(53,true),(41,true),(106,true)]
theorem der_31666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31666 :=
  CNF.rup_sound cl_31666 [cl_25905,cl_31658] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25905 v h) (hints_cons _ _ _ (der_31658 v h) (by intro d hd; cases hd)))
def cl_31667 : CNF.NClause := [(34,false),(47,false),(40,true),(53,true),(106,true)]
theorem der_31667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31667 :=
  CNF.rup_sound cl_31667 [cl_25906,cl_30063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25906 v h) (hints_cons _ _ _ (der_30063 v h) (by intro d hd; cases hd)))
def cl_31668 : CNF.NClause := [(40,false),(34,false),(53,true),(57,true),(106,true)]
theorem der_31668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31668 :=
  CNF.rup_sound cl_31668 [cl_25907,cl_30068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25907 v h) (hints_cons _ _ _ (der_30068 v h) (by intro d hd; cases hd)))
def cl_31669 : CNF.NClause := [(35,false),(52,false),(49,false),(38,true),(104,true)]
theorem der_31669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31669 :=
  CNF.rup_sound cl_31669 [cl_25908,cl_23832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25908 v h) (hints_cons _ _ _ (der_23832 v h) (by intro d hd; cases hd)))
def cl_31671 : CNF.NClause := [(35,false),(59,false),(38,true),(52,true),(104,true)]
theorem der_31671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31671 :=
  CNF.rup_sound cl_31671 [cl_25910,cl_30104] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25910 v h) (hints_cons _ _ _ (der_30104 v h) (by intro d hd; cases hd)))
def cl_31672 : CNF.NClause := [(50,false),(45,false),(55,false),(56,false),(94,true)]
theorem der_31672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31672 :=
  CNF.rup_sound cl_31672 [cl_25912,cl_25911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25912 v h) (hints_cons _ _ _ (der_25911 v h) (by intro d hd; cases hd)))
def cl_31674 : CNF.NClause := [(50,false),(55,false),(56,false),(40,true),(94,true)]
theorem der_31674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31674 :=
  CNF.rup_sound cl_31674 [cl_25914,cl_31672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25914 v h) (hints_cons _ _ _ (der_31672 v h) (by intro d hd; cases hd)))
def cl_31675 : CNF.NClause := [(40,false),(45,false),(55,false),(56,false),(94,true)]
theorem der_31675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31675 :=
  CNF.rup_sound cl_31675 [cl_25915,cl_31396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25915 v h) (hints_cons _ _ _ (der_31396 v h) (by intro d hd; cases hd)))
def cl_31677 : CNF.NClause := [(40,false),(55,false),(56,false),(35,true),(94,true)]
theorem der_31677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31677 :=
  CNF.rup_sound cl_31677 [cl_25917,cl_31675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25917 v h) (hints_cons _ _ _ (der_31675 v h) (by intro d hd; cases hd)))
def cl_31679 : CNF.NClause := [(50,false),(40,false),(45,false),(56,false),(94,true)]
theorem der_31679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31679 :=
  CNF.rup_sound cl_31679 [cl_25919,cl_31675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25919 v h) (hints_cons _ _ _ (der_31675 v h) (by intro d hd; cases hd)))
def cl_31681 : CNF.NClause := [(50,false),(40,false),(56,false),(55,true),(94,true)]
theorem der_31681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31681 :=
  CNF.rup_sound cl_31681 [cl_25921,cl_31679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25921 v h) (hints_cons _ _ _ (der_31679 v h) (by intro d hd; cases hd)))
def cl_31686 : CNF.NClause := [(50,false),(45,false),(55,false),(40,true),(94,true)]
theorem der_31686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31686 :=
  CNF.rup_sound cl_31686 [cl_25927,cl_31674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25927 v h) (hints_cons _ _ _ (der_31674 v h) (by intro d hd; cases hd)))
def cl_31688 : CNF.NClause := [(50,false),(55,false),(45,true),(40,true),(94,true)]
theorem der_31688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31688 :=
  CNF.rup_sound cl_31688 [cl_25929,cl_31674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25929 v h) (hints_cons _ _ _ (der_31674 v h) (by intro d hd; cases hd)))
def cl_31689 : CNF.NClause := [(40,false),(45,false),(55,false),(35,true),(94,true)]
theorem der_31689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31689 :=
  CNF.rup_sound cl_31689 [cl_25930,cl_25926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25930 v h) (hints_cons _ _ _ (der_25926 v h) (by intro d hd; cases hd)))
def cl_31690 : CNF.NClause := [(45,false),(55,false),(40,true),(35,true),(94,true)]
theorem der_31690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31690 :=
  CNF.rup_sound cl_31690 [cl_25931,cl_31686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25931 v h) (hints_cons _ _ _ (der_31686 v h) (by intro d hd; cases hd)))
def cl_31691 : CNF.NClause := [(40,false),(55,false),(45,true),(35,true),(94,true)]
theorem der_31691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31691 :=
  CNF.rup_sound cl_31691 [cl_25932,cl_31677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25932 v h) (hints_cons _ _ _ (der_31677 v h) (by intro d hd; cases hd)))
def cl_31692 : CNF.NClause := [(50,false),(40,false),(45,false),(55,true),(94,true)]
theorem der_31692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31692 :=
  CNF.rup_sound cl_31692 [cl_25933,cl_31679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25933 v h) (hints_cons _ _ _ (der_31679 v h) (by intro d hd; cases hd)))
def cl_31693 : CNF.NClause := [(50,false),(45,false),(40,true),(56,true),(94,true)]
theorem der_31693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31693 :=
  CNF.rup_sound cl_31693 [cl_25934,cl_31686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25934 v h) (hints_cons _ _ _ (der_31686 v h) (by intro d hd; cases hd)))
def cl_31694 : CNF.NClause := [(50,false),(40,false),(45,true),(55,true),(94,true)]
theorem der_31694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31694 :=
  CNF.rup_sound cl_31694 [cl_25935,cl_31681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25935 v h) (hints_cons _ _ _ (der_31681 v h) (by intro d hd; cases hd)))
def cl_31695 : CNF.NClause := [(40,false),(45,false),(55,true),(35,true),(94,true)]
theorem der_31695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31695 :=
  CNF.rup_sound cl_31695 [cl_25936,cl_31692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25936 v h) (hints_cons _ _ _ (der_31692 v h) (by intro d hd; cases hd)))
def cl_31696 : CNF.NClause := [(51,false),(60,false),(43,false),(47,false),(99,true)]
theorem der_31696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31696 :=
  CNF.rup_sound cl_31696 [cl_25938,cl_25937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25938 v h) (hints_cons _ _ _ (der_25937 v h) (by intro d hd; cases hd)))
def cl_31697 : CNF.NClause := [(51,false),(60,false),(39,false),(47,false),(99,true)]
theorem der_31697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31697 :=
  CNF.rup_sound cl_31697 [cl_25939,cl_25937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25939 v h) (hints_cons _ _ _ (der_25937 v h) (by intro d hd; cases hd)))
def cl_31698 : CNF.NClause := [(51,false),(60,false),(47,false),(39,true),(99,true)]
theorem der_31698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31698 :=
  CNF.rup_sound cl_31698 [cl_25940,cl_30746] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25940 v h) (hints_cons _ _ _ (der_30746 v h) (by intro d hd; cases hd)))
def cl_31699 : CNF.NClause := [(51,false),(60,false),(39,false),(43,false),(99,true)]
theorem der_31699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31699 :=
  CNF.rup_sound cl_31699 [cl_25941,cl_25937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25941 v h) (hints_cons _ _ _ (der_25937 v h) (by intro d hd; cases hd)))
def cl_31700 : CNF.NClause := [(51,false),(60,false),(43,false),(39,true),(99,true)]
theorem der_31700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31700 :=
  CNF.rup_sound cl_31700 [cl_25942,cl_31696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25942 v h) (hints_cons _ _ _ (der_31696 v h) (by intro d hd; cases hd)))
def cl_31701 : CNF.NClause := [(51,false),(60,false),(39,false),(43,true),(99,true)]
theorem der_31701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31701 :=
  CNF.rup_sound cl_31701 [cl_25943,cl_31697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25943 v h) (hints_cons _ _ _ (der_31697 v h) (by intro d hd; cases hd)))
def cl_31702 : CNF.NClause := [(51,false),(60,false),(47,true),(43,true),(99,true)]
theorem der_31702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31702 :=
  CNF.rup_sound cl_31702 [cl_25944,cl_31701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25944 v h) (hints_cons _ _ _ (der_31701 v h) (by intro d hd; cases hd)))
def cl_31703 : CNF.NClause := [(60,false),(47,false),(39,true),(43,false),(99,true)]
theorem der_31703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31703 :=
  CNF.rup_sound cl_31703 [cl_25946,cl_30747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25946 v h) (hints_cons _ _ _ (der_30747 v h) (by intro d hd; cases hd)))
def cl_31704 : CNF.NClause := [(60,false),(39,false),(47,false),(43,true),(99,true)]
theorem der_31704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31704 :=
  CNF.rup_sound cl_31704 [cl_25947,cl_31701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25947 v h) (hints_cons _ _ _ (der_31701 v h) (by intro d hd; cases hd)))
def cl_31705 : CNF.NClause := [(60,false),(47,false),(39,true),(51,true),(99,true)]
theorem der_31705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31705 :=
  CNF.rup_sound cl_31705 [cl_25948,cl_31703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25948 v h) (hints_cons _ _ _ (der_31703 v h) (by intro d hd; cases hd)))
def cl_31707 : CNF.NClause := [(60,false),(39,false),(47,true),(43,true),(99,true)]
theorem der_31707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31707 :=
  CNF.rup_sound cl_31707 [cl_25951,cl_31702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25951 v h) (hints_cons _ _ _ (der_31702 v h) (by intro d hd; cases hd)))
def cl_31708 : CNF.NClause := [(51,false),(99,true),(47,false),(39,true),(43,false)]
theorem der_31708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31708 :=
  CNF.rup_sound cl_31708 [cl_25953,cl_31696] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25953 v h) (hints_cons _ _ _ (der_31696 v h) (by intro d hd; cases hd)))
def cl_31709 : CNF.NClause := [(51,false),(39,false),(47,false),(43,true),(99,true)]
theorem der_31709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31709 :=
  CNF.rup_sound cl_31709 [cl_25954,cl_31701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25954 v h) (hints_cons _ _ _ (der_31701 v h) (by intro d hd; cases hd)))
def cl_31710 : CNF.NClause := [(51,false),(47,false),(39,true),(43,true),(99,true)]
theorem der_31710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31710 :=
  CNF.rup_sound cl_31710 [cl_25955,cl_30749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25955 v h) (hints_cons _ _ _ (der_30749 v h) (by intro d hd; cases hd)))
def cl_31711 : CNF.NClause := [(51,false),(39,false),(43,false),(47,true),(99,true)]
theorem der_31711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31711 :=
  CNF.rup_sound cl_31711 [cl_25956,cl_31699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25956 v h) (hints_cons _ _ _ (der_31699 v h) (by intro d hd; cases hd)))
def cl_31712 : CNF.NClause := [(51,false),(99,true),(47,true),(39,true),(43,false)]
theorem der_31712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31712 :=
  CNF.rup_sound cl_31712 [cl_25957,cl_31700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25957 v h) (hints_cons _ _ _ (der_31700 v h) (by intro d hd; cases hd)))
def cl_31713 : CNF.NClause := [(51,false),(39,false),(47,true),(43,true),(99,true)]
theorem der_31713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31713 :=
  CNF.rup_sound cl_31713 [cl_25958,cl_31701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25958 v h) (hints_cons _ _ _ (der_31701 v h) (by intro d hd; cases hd)))
def cl_31714 : CNF.NClause := [(39,false),(47,false),(43,false),(35,true),(99,true)]
theorem der_31714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31714 :=
  CNF.rup_sound cl_31714 [cl_25959,cl_25945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25959 v h) (hints_cons _ _ _ (der_25945 v h) (by intro d hd; cases hd)))
def cl_31715 : CNF.NClause := [(47,false),(39,true),(43,false),(51,true),(99,true)]
theorem der_31715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31715 :=
  CNF.rup_sound cl_31715 [cl_25960,cl_31703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25960 v h) (hints_cons _ _ _ (der_31703 v h) (by intro d hd; cases hd)))
def cl_31716 : CNF.NClause := [(39,false),(47,false),(43,true),(60,true),(99,true)]
theorem der_31716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31716 :=
  CNF.rup_sound cl_31716 [cl_25961,cl_31709] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25961 v h) (hints_cons _ _ _ (der_31709 v h) (by intro d hd; cases hd)))
def cl_31717 : CNF.NClause := [(39,false),(47,true),(43,false),(35,true),(99,true)]
theorem der_31717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31717 :=
  CNF.rup_sound cl_31717 [cl_25962,cl_31711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25962 v h) (hints_cons _ _ _ (der_31711 v h) (by intro d hd; cases hd)))
def cl_31718 : CNF.NClause := [(41,false),(59,false),(52,false),(49,false),(104,true)]
theorem der_31718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31718 :=
  CNF.rup_sound cl_31718 [cl_25964,cl_25963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25964 v h) (hints_cons _ _ _ (der_25963 v h) (by intro d hd; cases hd)))
def cl_31719 : CNF.NClause := [(59,false),(52,false),(49,false),(38,true),(104,true)]
theorem der_31719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31719 :=
  CNF.rup_sound cl_31719 [cl_25966,cl_31718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25966 v h) (hints_cons _ _ _ (der_31718 v h) (by intro d hd; cases hd)))
def cl_31720 : CNF.NClause := [(41,false),(59,false),(38,false),(52,false),(104,true)]
theorem der_31720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31720 :=
  CNF.rup_sound cl_31720 [cl_25967,cl_25963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25967 v h) (hints_cons _ _ _ (der_25963 v h) (by intro d hd; cases hd)))
def cl_31721 : CNF.NClause := [(41,false),(59,false),(52,false),(38,true),(104,true)]
theorem der_31721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31721 :=
  CNF.rup_sound cl_31721 [cl_25968,cl_31719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25968 v h) (hints_cons _ _ _ (der_31719 v h) (by intro d hd; cases hd)))
def cl_31722 : CNF.NClause := [(59,false),(38,false),(52,false),(35,true),(104,true)]
theorem der_31722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31722 :=
  CNF.rup_sound cl_31722 [cl_25969,cl_25965] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25969 v h) (hints_cons _ _ _ (der_25965 v h) (by intro d hd; cases hd)))
def cl_31723 : CNF.NClause := [(59,false),(52,false),(38,true),(41,true),(104,true)]
theorem der_31723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31723 :=
  CNF.rup_sound cl_31723 [cl_25970,cl_31719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25970 v h) (hints_cons _ _ _ (der_31719 v h) (by intro d hd; cases hd)))
def cl_31724 : CNF.NClause := [(41,false),(59,false),(38,false),(49,false),(104,true)]
theorem der_31724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31724 :=
  CNF.rup_sound cl_31724 [cl_25971,cl_25963] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25971 v h) (hints_cons _ _ _ (der_25963 v h) (by intro d hd; cases hd)))
def cl_31725 : CNF.NClause := [(41,false),(59,false),(49,false),(38,true),(104,true)]
theorem der_31725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31725 :=
  CNF.rup_sound cl_31725 [cl_25972,cl_31721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25972 v h) (hints_cons _ _ _ (der_31721 v h) (by intro d hd; cases hd)))
def cl_31726 : CNF.NClause := [(59,false),(38,false),(49,false),(35,true),(104,true)]
theorem der_31726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31726 :=
  CNF.rup_sound cl_31726 [cl_25973,cl_31724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25973 v h) (hints_cons _ _ _ (der_31724 v h) (by intro d hd; cases hd)))
def cl_31727 : CNF.NClause := [(59,false),(49,false),(38,true),(52,true),(104,true)]
theorem der_31727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31727 :=
  CNF.rup_sound cl_31727 [cl_25974,cl_31725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25974 v h) (hints_cons _ _ _ (der_31725 v h) (by intro d hd; cases hd)))
def cl_31728 : CNF.NClause := [(41,false),(59,false),(38,false),(52,true),(104,true)]
theorem der_31728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31728 :=
  CNF.rup_sound cl_31728 [cl_25975,cl_31724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25975 v h) (hints_cons _ _ _ (der_31724 v h) (by intro d hd; cases hd)))
def cl_31729 : CNF.NClause := [(41,false),(59,false),(49,true),(38,true),(104,true)]
theorem der_31729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31729 :=
  CNF.rup_sound cl_31729 [cl_25976,cl_31721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25976 v h) (hints_cons _ _ _ (der_31721 v h) (by intro d hd; cases hd)))
def cl_31730 : CNF.NClause := [(59,false),(38,false),(49,true),(35,true),(104,true)]
theorem der_31730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31730 :=
  CNF.rup_sound cl_31730 [cl_25977,cl_31722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25977 v h) (hints_cons _ _ _ (der_31722 v h) (by intro d hd; cases hd)))
def cl_31731 : CNF.NClause := [(41,false),(38,false),(52,false),(49,false),(104,true)]
theorem der_31731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31731 :=
  CNF.rup_sound cl_31731 [cl_25978,cl_31724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25978 v h) (hints_cons _ _ _ (der_31724 v h) (by intro d hd; cases hd)))
def cl_31732 : CNF.NClause := [(41,false),(52,false),(49,false),(38,true),(104,true)]
theorem der_31732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31732 :=
  CNF.rup_sound cl_31732 [cl_25979,cl_31721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25979 v h) (hints_cons _ _ _ (der_31721 v h) (by intro d hd; cases hd)))
def cl_31733 : CNF.NClause := [(38,false),(52,false),(49,false),(41,true),(104,true)]
theorem der_31733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31733 :=
  CNF.rup_sound cl_31733 [cl_25980,cl_23824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25980 v h) (hints_cons _ _ _ (der_23824 v h) (by intro d hd; cases hd)))
def cl_31734 : CNF.NClause := [(41,false),(38,false),(52,false),(59,true),(104,true)]
theorem der_31734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31734 :=
  CNF.rup_sound cl_31734 [cl_25982,cl_31731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25982 v h) (hints_cons _ _ _ (der_31731 v h) (by intro d hd; cases hd)))
def cl_31735 : CNF.NClause := [(41,false),(52,false),(38,true),(35,true),(104,true)]
theorem der_31735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_31735 :=
  CNF.rup_sound cl_31735 [cl_25983,cl_31732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25983 v h) (hints_cons _ _ _ (der_31732 v h) (by intro d hd; cases hd)))
def chunk017 : List CNF.NClause := [cl_31095,cl_31098,cl_31100,cl_31101,cl_31104,cl_31108,cl_31112,cl_31113,cl_31114,cl_31118,cl_31119,cl_31121,cl_31124,cl_31126,cl_31127,cl_31128,cl_31131,cl_31132,cl_31133,cl_31135,cl_31140,cl_31142,cl_31143,cl_31145,cl_31146,cl_31151,cl_31152,cl_31153,cl_31156,cl_31160,cl_31161,cl_31162,cl_31164,cl_31165,cl_31166,cl_31168,cl_31169,cl_31170,cl_31171,cl_31172,cl_31173,cl_31174,cl_31175,cl_31177,cl_31179,cl_31180,cl_31184,cl_31185,cl_31186,cl_31187,cl_31188,cl_31189,cl_31190,cl_31191,cl_31192,cl_31193,cl_31196,cl_31197,cl_31198,cl_31199,cl_31200,cl_31201,cl_31202,cl_31203,cl_31204,cl_31205,cl_31206,cl_31207,cl_31208,cl_31209,cl_31210,cl_31211,cl_31212,cl_31213,cl_31214,cl_31215,cl_31216,cl_31217,cl_31218,cl_31219,cl_31221,cl_31225,cl_31227,cl_31228,cl_31229,cl_31230,cl_31231,cl_31232,cl_31233,cl_31234,cl_31235,cl_31236,cl_31237,cl_31239,cl_31240,cl_31242,cl_31243,cl_31244,cl_31245,cl_31246,cl_31247,cl_31248,cl_31249,cl_31250,cl_31251,cl_31252,cl_31253,cl_31254,cl_31255,cl_31256,cl_31257,cl_31258,cl_31259,cl_31261,cl_31262,cl_31264,cl_31265,cl_31267,cl_31268,cl_31269,cl_31270,cl_31271,cl_31272,cl_31273,cl_31274,cl_31275,cl_31276,cl_31277,cl_31278,cl_31279,cl_31280,cl_31281,cl_31282,cl_31283,cl_31284,cl_31285,cl_31288,cl_31289,cl_31290,cl_31291,cl_31292,cl_31293,cl_31294,cl_31295,cl_31296,cl_31297,cl_31299,cl_31300,cl_31301,cl_31302,cl_31303,cl_31304,cl_31305,cl_31306,cl_31307,cl_31308,cl_31309,cl_31310,cl_31311,cl_31312,cl_31313,cl_31314,cl_31315,cl_31316,cl_31317,cl_31318,cl_31320,cl_31321,cl_31322,cl_31323,cl_31324,cl_31325,cl_31326,cl_31331,cl_31332,cl_31333,cl_31334,cl_31335,cl_31336,cl_31337,cl_31338,cl_31339,cl_31340,cl_31341,cl_31342,cl_31343,cl_31344,cl_31345,cl_31346,cl_31347,cl_31348,cl_31349,cl_31350,cl_31351,cl_31352,cl_31353,cl_31356,cl_31357,cl_31358,cl_31360,cl_31362,cl_31364,cl_31366,cl_31367,cl_31368,cl_31370,cl_31371,cl_31372,cl_31374,cl_31376,cl_31378,cl_31381,cl_31382,cl_31383,cl_31384,cl_31387,cl_31392,cl_31393,cl_31396,cl_31399,cl_31400,cl_31401,cl_31402,cl_31403,cl_31405,cl_31407,cl_31408,cl_31409,cl_31411,cl_31412,cl_31414,cl_31415,cl_31416,cl_31417,cl_31418,cl_31419,cl_31420,cl_31421,cl_31422,cl_31424,cl_31425,cl_31426,cl_31427,cl_31431,cl_31432,cl_31433,cl_31434,cl_31435,cl_31436,cl_31437,cl_31438,cl_31439,cl_31440,cl_31441,cl_31442,cl_31443,cl_31444,cl_31445,cl_31446,cl_31447,cl_31448,cl_31449,cl_31450,cl_31451,cl_31452,cl_31454,cl_31455,cl_31456,cl_31458,cl_31460,cl_31463,cl_31465,cl_31466,cl_31467,cl_31468,cl_31469,cl_31470,cl_31471,cl_31472,cl_31473,cl_31474,cl_31475,cl_31476,cl_31477,cl_31479,cl_31480,cl_31481,cl_31482,cl_31483,cl_31484,cl_31485,cl_31486,cl_31487,cl_31488,cl_31489,cl_31490,cl_31491,cl_31492,cl_31493,cl_31495,cl_31496,cl_31497,cl_31498,cl_31499,cl_31501,cl_31502,cl_31503,cl_31504,cl_31505,cl_31506,cl_31507,cl_31508,cl_31509,cl_31510,cl_31511,cl_31512,cl_31513,cl_31514,cl_31515,cl_31518,cl_31519,cl_31520,cl_31521,cl_31522,cl_31523,cl_31524,cl_31525,cl_31526,cl_31527,cl_31528,cl_31529,cl_31530,cl_31531,cl_31532,cl_31533,cl_31534,cl_31536,cl_31537,cl_31538,cl_31539,cl_31540,cl_31541,cl_31542,cl_31543,cl_31544,cl_31545,cl_31546,cl_31547,cl_31548,cl_31549,cl_31550,cl_31551,cl_31552,cl_31553,cl_31554,cl_31555,cl_31556,cl_31558,cl_31559,cl_31560,cl_31561,cl_31562,cl_31564,cl_31565,cl_31567,cl_31568,cl_31569,cl_31570,cl_31571,cl_31572,cl_31573,cl_31574,cl_31575,cl_31577,cl_31578,cl_31579,cl_31580,cl_31581,cl_31582,cl_31583,cl_31584,cl_31585,cl_31586,cl_31589,cl_31590,cl_31591,cl_31592,cl_31593,cl_31594,cl_31595,cl_31597,cl_31599,cl_31600,cl_31603,cl_31605,cl_31606,cl_31609,cl_31610,cl_31611,cl_31612,cl_31613,cl_31614,cl_31615,cl_31619,cl_31622,cl_31623,cl_31624,cl_31625,cl_31626,cl_31627,cl_31628,cl_31629,cl_31630,cl_31633,cl_31634,cl_31635,cl_31636,cl_31637,cl_31638,cl_31639,cl_31640,cl_31642,cl_31643,cl_31644,cl_31645,cl_31646,cl_31647,cl_31648,cl_31649,cl_31650,cl_31651,cl_31652,cl_31653,cl_31655,cl_31657,cl_31658,cl_31660,cl_31661,cl_31662,cl_31664,cl_31665,cl_31666,cl_31667,cl_31668,cl_31669,cl_31671,cl_31672,cl_31674,cl_31675,cl_31677,cl_31679,cl_31681,cl_31686,cl_31688,cl_31689,cl_31690,cl_31691,cl_31692,cl_31693,cl_31694,cl_31695,cl_31696,cl_31697,cl_31698,cl_31699,cl_31700,cl_31701,cl_31702,cl_31703,cl_31704,cl_31705,cl_31707,cl_31708,cl_31709,cl_31710,cl_31711,cl_31712,cl_31713,cl_31714,cl_31715,cl_31716,cl_31717,cl_31718,cl_31719,cl_31720,cl_31721,cl_31722,cl_31723,cl_31724,cl_31725,cl_31726,cl_31727,cl_31728,cl_31729,cl_31730,cl_31731,cl_31732,cl_31733,cl_31734,cl_31735]
theorem chunk_sound017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk017, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_31095 v h) (hints_cons _ _ _ (der_31098 v h) (hints_cons _ _ _ (der_31100 v h) (hints_cons _ _ _ (der_31101 v h) (hints_cons _ _ _ (der_31104 v h) (hints_cons _ _ _ (der_31108 v h) (hints_cons _ _ _ (der_31112 v h) (hints_cons _ _ _ (der_31113 v h) (hints_cons _ _ _ (der_31114 v h) (hints_cons _ _ _ (der_31118 v h) (hints_cons _ _ _ (der_31119 v h) (hints_cons _ _ _ (der_31121 v h) (hints_cons _ _ _ (der_31124 v h) (hints_cons _ _ _ (der_31126 v h) (hints_cons _ _ _ (der_31127 v h) (hints_cons _ _ _ (der_31128 v h) (hints_cons _ _ _ (der_31131 v h) (hints_cons _ _ _ (der_31132 v h) (hints_cons _ _ _ (der_31133 v h) (hints_cons _ _ _ (der_31135 v h) (hints_cons _ _ _ (der_31140 v h) (hints_cons _ _ _ (der_31142 v h) (hints_cons _ _ _ (der_31143 v h) (hints_cons _ _ _ (der_31145 v h) (hints_cons _ _ _ (der_31146 v h) (hints_cons _ _ _ (der_31151 v h) (hints_cons _ _ _ (der_31152 v h) (hints_cons _ _ _ (der_31153 v h) (hints_cons _ _ _ (der_31156 v h) (hints_cons _ _ _ (der_31160 v h) (hints_cons _ _ _ (der_31161 v h) (hints_cons _ _ _ (der_31162 v h) (hints_cons _ _ _ (der_31164 v h) (hints_cons _ _ _ (der_31165 v h) (hints_cons _ _ _ (der_31166 v h) (hints_cons _ _ _ (der_31168 v h) (hints_cons _ _ _ (der_31169 v h) (hints_cons _ _ _ (der_31170 v h) (hints_cons _ _ _ (der_31171 v h) (hints_cons _ _ _ (der_31172 v h) (hints_cons _ _ _ (der_31173 v h) (hints_cons _ _ _ (der_31174 v h) (hints_cons _ _ _ (der_31175 v h) (hints_cons _ _ _ (der_31177 v h) (hints_cons _ _ _ (der_31179 v h) (hints_cons _ _ _ (der_31180 v h) (hints_cons _ _ _ (der_31184 v h) (hints_cons _ _ _ (der_31185 v h) (hints_cons _ _ _ (der_31186 v h) (hints_cons _ _ _ (der_31187 v h) (hints_cons _ _ _ (der_31188 v h) (hints_cons _ _ _ (der_31189 v h) (hints_cons _ _ _ (der_31190 v h) (hints_cons _ _ _ (der_31191 v h) (hints_cons _ _ _ (der_31192 v h) (hints_cons _ _ _ (der_31193 v h) (hints_cons _ _ _ (der_31196 v h) (hints_cons _ _ _ (der_31197 v h) (hints_cons _ _ _ (der_31198 v h) (hints_cons _ _ _ (der_31199 v h) (hints_cons _ _ _ (der_31200 v h) (hints_cons _ _ _ (der_31201 v h) (hints_cons _ _ _ (der_31202 v h) (hints_cons _ _ _ (der_31203 v h) (hints_cons _ _ _ (der_31204 v h) (hints_cons _ _ _ (der_31205 v h) (hints_cons _ _ _ (der_31206 v h) (hints_cons _ _ _ (der_31207 v h) (hints_cons _ _ _ (der_31208 v h) (hints_cons _ _ _ (der_31209 v h) (hints_cons _ _ _ (der_31210 v h) (hints_cons _ _ _ (der_31211 v h) (hints_cons _ _ _ (der_31212 v h) (hints_cons _ _ _ (der_31213 v h) (hints_cons _ _ _ (der_31214 v h) (hints_cons _ _ _ (der_31215 v h) (hints_cons _ _ _ (der_31216 v h) (hints_cons _ _ _ (der_31217 v h) (hints_cons _ _ _ (der_31218 v h) (hints_cons _ _ _ (der_31219 v h) (hints_cons _ _ _ (der_31221 v h) (hints_cons _ _ _ (der_31225 v h) (hints_cons _ _ _ (der_31227 v h) (hints_cons _ _ _ (der_31228 v h) (hints_cons _ _ _ (der_31229 v h) (hints_cons _ _ _ (der_31230 v h) (hints_cons _ _ _ (der_31231 v h) (hints_cons _ _ _ (der_31232 v h) (hints_cons _ _ _ (der_31233 v h) (hints_cons _ _ _ (der_31234 v h) (hints_cons _ _ _ (der_31235 v h) (hints_cons _ _ _ (der_31236 v h) (hints_cons _ _ _ (der_31237 v h) (hints_cons _ _ _ (der_31239 v h) (hints_cons _ _ _ (der_31240 v h) (hints_cons _ _ _ (der_31242 v h) (hints_cons _ _ _ (der_31243 v h) (hints_cons _ _ _ (der_31244 v h) (hints_cons _ _ _ (der_31245 v h) (hints_cons _ _ _ (der_31246 v h) (hints_cons _ _ _ (der_31247 v h) (hints_cons _ _ _ (der_31248 v h) (hints_cons _ _ _ (der_31249 v h) (hints_cons _ _ _ (der_31250 v h) (hints_cons _ _ _ (der_31251 v h) (hints_cons _ _ _ (der_31252 v h) (hints_cons _ _ _ (der_31253 v h) (hints_cons _ _ _ (der_31254 v h) (hints_cons _ _ _ (der_31255 v h) (hints_cons _ _ _ (der_31256 v h) (hints_cons _ _ _ (der_31257 v h) (hints_cons _ _ _ (der_31258 v h) (hints_cons _ _ _ (der_31259 v h) (hints_cons _ _ _ (der_31261 v h) (hints_cons _ _ _ (der_31262 v h) (hints_cons _ _ _ (der_31264 v h) (hints_cons _ _ _ (der_31265 v h) (hints_cons _ _ _ (der_31267 v h) (hints_cons _ _ _ (der_31268 v h) (hints_cons _ _ _ (der_31269 v h) (hints_cons _ _ _ (der_31270 v h) (hints_cons _ _ _ (der_31271 v h) (hints_cons _ _ _ (der_31272 v h) (hints_cons _ _ _ (der_31273 v h) (hints_cons _ _ _ (der_31274 v h) (hints_cons _ _ _ (der_31275 v h) (hints_cons _ _ _ (der_31276 v h) (hints_cons _ _ _ (der_31277 v h) (hints_cons _ _ _ (der_31278 v h) (hints_cons _ _ _ (der_31279 v h) (hints_cons _ _ _ (der_31280 v h) (hints_cons _ _ _ (der_31281 v h) (hints_cons _ _ _ (der_31282 v h) (hints_cons _ _ _ (der_31283 v h) (hints_cons _ _ _ (der_31284 v h) (hints_cons _ _ _ (der_31285 v h) (hints_cons _ _ _ (der_31288 v h) (hints_cons _ _ _ (der_31289 v h) (hints_cons _ _ _ (der_31290 v h) (hints_cons _ _ _ (der_31291 v h) (hints_cons _ _ _ (der_31292 v h) (hints_cons _ _ _ (der_31293 v h) (hints_cons _ _ _ (der_31294 v h) (hints_cons _ _ _ (der_31295 v h) (hints_cons _ _ _ (der_31296 v h) (hints_cons _ _ _ (der_31297 v h) (hints_cons _ _ _ (der_31299 v h) (hints_cons _ _ _ (der_31300 v h) (hints_cons _ _ _ (der_31301 v h) (hints_cons _ _ _ (der_31302 v h) (hints_cons _ _ _ (der_31303 v h) (hints_cons _ _ _ (der_31304 v h) (hints_cons _ _ _ (der_31305 v h) (hints_cons _ _ _ (der_31306 v h) (hints_cons _ _ _ (der_31307 v h) (hints_cons _ _ _ (der_31308 v h) (hints_cons _ _ _ (der_31309 v h) (hints_cons _ _ _ (der_31310 v h) (hints_cons _ _ _ (der_31311 v h) (hints_cons _ _ _ (der_31312 v h) (hints_cons _ _ _ (der_31313 v h) (hints_cons _ _ _ (der_31314 v h) (hints_cons _ _ _ (der_31315 v h) (hints_cons _ _ _ (der_31316 v h) (hints_cons _ _ _ (der_31317 v h) (hints_cons _ _ _ (der_31318 v h) (hints_cons _ _ _ (der_31320 v h) (hints_cons _ _ _ (der_31321 v h) (hints_cons _ _ _ (der_31322 v h) (hints_cons _ _ _ (der_31323 v h) (hints_cons _ _ _ (der_31324 v h) (hints_cons _ _ _ (der_31325 v h) (hints_cons _ _ _ (der_31326 v h) (hints_cons _ _ _ (der_31331 v h) (hints_cons _ _ _ (der_31332 v h) (hints_cons _ _ _ (der_31333 v h) (hints_cons _ _ _ (der_31334 v h) (hints_cons _ _ _ (der_31335 v h) (hints_cons _ _ _ (der_31336 v h) (hints_cons _ _ _ (der_31337 v h) (hints_cons _ _ _ (der_31338 v h) (hints_cons _ _ _ (der_31339 v h) (hints_cons _ _ _ (der_31340 v h) (hints_cons _ _ _ (der_31341 v h) (hints_cons _ _ _ (der_31342 v h) (hints_cons _ _ _ (der_31343 v h) (hints_cons _ _ _ (der_31344 v h) (hints_cons _ _ _ (der_31345 v h) (hints_cons _ _ _ (der_31346 v h) (hints_cons _ _ _ (der_31347 v h) (hints_cons _ _ _ (der_31348 v h) (hints_cons _ _ _ (der_31349 v h) (hints_cons _ _ _ (der_31350 v h) (hints_cons _ _ _ (der_31351 v h) (hints_cons _ _ _ (der_31352 v h) (hints_cons _ _ _ (der_31353 v h) (hints_cons _ _ _ (der_31356 v h) (hints_cons _ _ _ (der_31357 v h) (hints_cons _ _ _ (der_31358 v h) (hints_cons _ _ _ (der_31360 v h) (hints_cons _ _ _ (der_31362 v h) (hints_cons _ _ _ (der_31364 v h) (hints_cons _ _ _ (der_31366 v h) (hints_cons _ _ _ (der_31367 v h) (hints_cons _ _ _ (der_31368 v h) (hints_cons _ _ _ (der_31370 v h) (hints_cons _ _ _ (der_31371 v h) (hints_cons _ _ _ (der_31372 v h) (hints_cons _ _ _ (der_31374 v h) (hints_cons _ _ _ (der_31376 v h) (hints_cons _ _ _ (der_31378 v h) (hints_cons _ _ _ (der_31381 v h) (hints_cons _ _ _ (der_31382 v h) (hints_cons _ _ _ (der_31383 v h) (hints_cons _ _ _ (der_31384 v h) (hints_cons _ _ _ (der_31387 v h) (hints_cons _ _ _ (der_31392 v h) (hints_cons _ _ _ (der_31393 v h) (hints_cons _ _ _ (der_31396 v h) (hints_cons _ _ _ (der_31399 v h) (hints_cons _ _ _ (der_31400 v h) (hints_cons _ _ _ (der_31401 v h) (hints_cons _ _ _ (der_31402 v h) (hints_cons _ _ _ (der_31403 v h) (hints_cons _ _ _ (der_31405 v h) (hints_cons _ _ _ (der_31407 v h) (hints_cons _ _ _ (der_31408 v h) (hints_cons _ _ _ (der_31409 v h) (hints_cons _ _ _ (der_31411 v h) (hints_cons _ _ _ (der_31412 v h) (hints_cons _ _ _ (der_31414 v h) (hints_cons _ _ _ (der_31415 v h) (hints_cons _ _ _ (der_31416 v h) (hints_cons _ _ _ (der_31417 v h) (hints_cons _ _ _ (der_31418 v h) (hints_cons _ _ _ (der_31419 v h) (hints_cons _ _ _ (der_31420 v h) (hints_cons _ _ _ (der_31421 v h) (hints_cons _ _ _ (der_31422 v h) (hints_cons _ _ _ (der_31424 v h) (hints_cons _ _ _ (der_31425 v h) (hints_cons _ _ _ (der_31426 v h) (hints_cons _ _ _ (der_31427 v h) (hints_cons _ _ _ (der_31431 v h) (hints_cons _ _ _ (der_31432 v h) (hints_cons _ _ _ (der_31433 v h) (hints_cons _ _ _ (der_31434 v h) (hints_cons _ _ _ (der_31435 v h) (hints_cons _ _ _ (der_31436 v h) (hints_cons _ _ _ (der_31437 v h) (hints_cons _ _ _ (der_31438 v h) (hints_cons _ _ _ (der_31439 v h) (hints_cons _ _ _ (der_31440 v h) (hints_cons _ _ _ (der_31441 v h) (hints_cons _ _ _ (der_31442 v h) (hints_cons _ _ _ (der_31443 v h) (hints_cons _ _ _ (der_31444 v h) (hints_cons _ _ _ (der_31445 v h) (hints_cons _ _ _ (der_31446 v h) (hints_cons _ _ _ (der_31447 v h) (hints_cons _ _ _ (der_31448 v h) (hints_cons _ _ _ (der_31449 v h) (hints_cons _ _ _ (der_31450 v h) (hints_cons _ _ _ (der_31451 v h) (hints_cons _ _ _ (der_31452 v h) (hints_cons _ _ _ (der_31454 v h) (hints_cons _ _ _ (der_31455 v h) (hints_cons _ _ _ (der_31456 v h) (hints_cons _ _ _ (der_31458 v h) (hints_cons _ _ _ (der_31460 v h) (hints_cons _ _ _ (der_31463 v h) (hints_cons _ _ _ (der_31465 v h) (hints_cons _ _ _ (der_31466 v h) (hints_cons _ _ _ (der_31467 v h) (hints_cons _ _ _ (der_31468 v h) (hints_cons _ _ _ (der_31469 v h) (hints_cons _ _ _ (der_31470 v h) (hints_cons _ _ _ (der_31471 v h) (hints_cons _ _ _ (der_31472 v h) (hints_cons _ _ _ (der_31473 v h) (hints_cons _ _ _ (der_31474 v h) (hints_cons _ _ _ (der_31475 v h) (hints_cons _ _ _ (der_31476 v h) (hints_cons _ _ _ (der_31477 v h) (hints_cons _ _ _ (der_31479 v h) (hints_cons _ _ _ (der_31480 v h) (hints_cons _ _ _ (der_31481 v h) (hints_cons _ _ _ (der_31482 v h) (hints_cons _ _ _ (der_31483 v h) (hints_cons _ _ _ (der_31484 v h) (hints_cons _ _ _ (der_31485 v h) (hints_cons _ _ _ (der_31486 v h) (hints_cons _ _ _ (der_31487 v h) (hints_cons _ _ _ (der_31488 v h) (hints_cons _ _ _ (der_31489 v h) (hints_cons _ _ _ (der_31490 v h) (hints_cons _ _ _ (der_31491 v h) (hints_cons _ _ _ (der_31492 v h) (hints_cons _ _ _ (der_31493 v h) (hints_cons _ _ _ (der_31495 v h) (hints_cons _ _ _ (der_31496 v h) (hints_cons _ _ _ (der_31497 v h) (hints_cons _ _ _ (der_31498 v h) (hints_cons _ _ _ (der_31499 v h) (hints_cons _ _ _ (der_31501 v h) (hints_cons _ _ _ (der_31502 v h) (hints_cons _ _ _ (der_31503 v h) (hints_cons _ _ _ (der_31504 v h) (hints_cons _ _ _ (der_31505 v h) (hints_cons _ _ _ (der_31506 v h) (hints_cons _ _ _ (der_31507 v h) (hints_cons _ _ _ (der_31508 v h) (hints_cons _ _ _ (der_31509 v h) (hints_cons _ _ _ (der_31510 v h) (hints_cons _ _ _ (der_31511 v h) (hints_cons _ _ _ (der_31512 v h) (hints_cons _ _ _ (der_31513 v h) (hints_cons _ _ _ (der_31514 v h) (hints_cons _ _ _ (der_31515 v h) (hints_cons _ _ _ (der_31518 v h) (hints_cons _ _ _ (der_31519 v h) (hints_cons _ _ _ (der_31520 v h) (hints_cons _ _ _ (der_31521 v h) (hints_cons _ _ _ (der_31522 v h) (hints_cons _ _ _ (der_31523 v h) (hints_cons _ _ _ (der_31524 v h) (hints_cons _ _ _ (der_31525 v h) (hints_cons _ _ _ (der_31526 v h) (hints_cons _ _ _ (der_31527 v h) (hints_cons _ _ _ (der_31528 v h) (hints_cons _ _ _ (der_31529 v h) (hints_cons _ _ _ (der_31530 v h) (hints_cons _ _ _ (der_31531 v h) (hints_cons _ _ _ (der_31532 v h) (hints_cons _ _ _ (der_31533 v h) (hints_cons _ _ _ (der_31534 v h) (hints_cons _ _ _ (der_31536 v h) (hints_cons _ _ _ (der_31537 v h) (hints_cons _ _ _ (der_31538 v h) (hints_cons _ _ _ (der_31539 v h) (hints_cons _ _ _ (der_31540 v h) (hints_cons _ _ _ (der_31541 v h) (hints_cons _ _ _ (der_31542 v h) (hints_cons _ _ _ (der_31543 v h) (hints_cons _ _ _ (der_31544 v h) (hints_cons _ _ _ (der_31545 v h) (hints_cons _ _ _ (der_31546 v h) (hints_cons _ _ _ (der_31547 v h) (hints_cons _ _ _ (der_31548 v h) (hints_cons _ _ _ (der_31549 v h) (hints_cons _ _ _ (der_31550 v h) (hints_cons _ _ _ (der_31551 v h) (hints_cons _ _ _ (der_31552 v h) (hints_cons _ _ _ (der_31553 v h) (hints_cons _ _ _ (der_31554 v h) (hints_cons _ _ _ (der_31555 v h) (hints_cons _ _ _ (der_31556 v h) (hints_cons _ _ _ (der_31558 v h) (hints_cons _ _ _ (der_31559 v h) (hints_cons _ _ _ (der_31560 v h) (hints_cons _ _ _ (der_31561 v h) (hints_cons _ _ _ (der_31562 v h) (hints_cons _ _ _ (der_31564 v h) (hints_cons _ _ _ (der_31565 v h) (hints_cons _ _ _ (der_31567 v h) (hints_cons _ _ _ (der_31568 v h) (hints_cons _ _ _ (der_31569 v h) (hints_cons _ _ _ (der_31570 v h) (hints_cons _ _ _ (der_31571 v h) (hints_cons _ _ _ (der_31572 v h) (hints_cons _ _ _ (der_31573 v h) (hints_cons _ _ _ (der_31574 v h) (hints_cons _ _ _ (der_31575 v h) (hints_cons _ _ _ (der_31577 v h) (hints_cons _ _ _ (der_31578 v h) (hints_cons _ _ _ (der_31579 v h) (hints_cons _ _ _ (der_31580 v h) (hints_cons _ _ _ (der_31581 v h) (hints_cons _ _ _ (der_31582 v h) (hints_cons _ _ _ (der_31583 v h) (hints_cons _ _ _ (der_31584 v h) (hints_cons _ _ _ (der_31585 v h) (hints_cons _ _ _ (der_31586 v h) (hints_cons _ _ _ (der_31589 v h) (hints_cons _ _ _ (der_31590 v h) (hints_cons _ _ _ (der_31591 v h) (hints_cons _ _ _ (der_31592 v h) (hints_cons _ _ _ (der_31593 v h) (hints_cons _ _ _ (der_31594 v h) (hints_cons _ _ _ (der_31595 v h) (hints_cons _ _ _ (der_31597 v h) (hints_cons _ _ _ (der_31599 v h) (hints_cons _ _ _ (der_31600 v h) (hints_cons _ _ _ (der_31603 v h) (hints_cons _ _ _ (der_31605 v h) (hints_cons _ _ _ (der_31606 v h) (hints_cons _ _ _ (der_31609 v h) (hints_cons _ _ _ (der_31610 v h) (hints_cons _ _ _ (der_31611 v h) (hints_cons _ _ _ (der_31612 v h) (hints_cons _ _ _ (der_31613 v h) (hints_cons _ _ _ (der_31614 v h) (hints_cons _ _ _ (der_31615 v h) (hints_cons _ _ _ (der_31619 v h) (hints_cons _ _ _ (der_31622 v h) (hints_cons _ _ _ (der_31623 v h) (hints_cons _ _ _ (der_31624 v h) (hints_cons _ _ _ (der_31625 v h) (hints_cons _ _ _ (der_31626 v h) (hints_cons _ _ _ (der_31627 v h) (hints_cons _ _ _ (der_31628 v h) (hints_cons _ _ _ (der_31629 v h) (hints_cons _ _ _ (der_31630 v h) (hints_cons _ _ _ (der_31633 v h) (hints_cons _ _ _ (der_31634 v h) (hints_cons _ _ _ (der_31635 v h) (hints_cons _ _ _ (der_31636 v h) (hints_cons _ _ _ (der_31637 v h) (hints_cons _ _ _ (der_31638 v h) (hints_cons _ _ _ (der_31639 v h) (hints_cons _ _ _ (der_31640 v h) (hints_cons _ _ _ (der_31642 v h) (hints_cons _ _ _ (der_31643 v h) (hints_cons _ _ _ (der_31644 v h) (hints_cons _ _ _ (der_31645 v h) (hints_cons _ _ _ (der_31646 v h) (hints_cons _ _ _ (der_31647 v h) (hints_cons _ _ _ (der_31648 v h) (hints_cons _ _ _ (der_31649 v h) (hints_cons _ _ _ (der_31650 v h) (hints_cons _ _ _ (der_31651 v h) (hints_cons _ _ _ (der_31652 v h) (hints_cons _ _ _ (der_31653 v h) (hints_cons _ _ _ (der_31655 v h) (hints_cons _ _ _ (der_31657 v h) (hints_cons _ _ _ (der_31658 v h) (hints_cons _ _ _ (der_31660 v h) (hints_cons _ _ _ (der_31661 v h) (hints_cons _ _ _ (der_31662 v h) (hints_cons _ _ _ (der_31664 v h) (hints_cons _ _ _ (der_31665 v h) (hints_cons _ _ _ (der_31666 v h) (hints_cons _ _ _ (der_31667 v h) (hints_cons _ _ _ (der_31668 v h) (hints_cons _ _ _ (der_31669 v h) (hints_cons _ _ _ (der_31671 v h) (hints_cons _ _ _ (der_31672 v h) (hints_cons _ _ _ (der_31674 v h) (hints_cons _ _ _ (der_31675 v h) (hints_cons _ _ _ (der_31677 v h) (hints_cons _ _ _ (der_31679 v h) (hints_cons _ _ _ (der_31681 v h) (hints_cons _ _ _ (der_31686 v h) (hints_cons _ _ _ (der_31688 v h) (hints_cons _ _ _ (der_31689 v h) (hints_cons _ _ _ (der_31690 v h) (hints_cons _ _ _ (der_31691 v h) (hints_cons _ _ _ (der_31692 v h) (hints_cons _ _ _ (der_31693 v h) (hints_cons _ _ _ (der_31694 v h) (hints_cons _ _ _ (der_31695 v h) (hints_cons _ _ _ (der_31696 v h) (hints_cons _ _ _ (der_31697 v h) (hints_cons _ _ _ (der_31698 v h) (hints_cons _ _ _ (der_31699 v h) (hints_cons _ _ _ (der_31700 v h) (hints_cons _ _ _ (der_31701 v h) (hints_cons _ _ _ (der_31702 v h) (hints_cons _ _ _ (der_31703 v h) (hints_cons _ _ _ (der_31704 v h) (hints_cons _ _ _ (der_31705 v h) (hints_cons _ _ _ (der_31707 v h) (hints_cons _ _ _ (der_31708 v h) (hints_cons _ _ _ (der_31709 v h) (hints_cons _ _ _ (der_31710 v h) (hints_cons _ _ _ (der_31711 v h) (hints_cons _ _ _ (der_31712 v h) (hints_cons _ _ _ (der_31713 v h) (hints_cons _ _ _ (der_31714 v h) (hints_cons _ _ _ (der_31715 v h) (hints_cons _ _ _ (der_31716 v h) (hints_cons _ _ _ (der_31717 v h) (hints_cons _ _ _ (der_31718 v h) (hints_cons _ _ _ (der_31719 v h) (hints_cons _ _ _ (der_31720 v h) (hints_cons _ _ _ (der_31721 v h) (hints_cons _ _ _ (der_31722 v h) (hints_cons _ _ _ (der_31723 v h) (hints_cons _ _ _ (der_31724 v h) (hints_cons _ _ _ (der_31725 v h) (hints_cons _ _ _ (der_31726 v h) (hints_cons _ _ _ (der_31727 v h) (hints_cons _ _ _ (der_31728 v h) (hints_cons _ _ _ (der_31729 v h) (hints_cons _ _ _ (der_31730 v h) (hints_cons _ _ _ (der_31731 v h) (hints_cons _ _ _ (der_31732 v h) (hints_cons _ _ _ (der_31733 v h) (hints_cons _ _ _ (der_31734 v h) (hints_cons _ _ _ (der_31735 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix017 := prefix016 ++ chunk017
theorem prefix_sound017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix017, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound016 v h c hc
  · exact chunk_sound017 v h c hc
end Percolation.NReplay
