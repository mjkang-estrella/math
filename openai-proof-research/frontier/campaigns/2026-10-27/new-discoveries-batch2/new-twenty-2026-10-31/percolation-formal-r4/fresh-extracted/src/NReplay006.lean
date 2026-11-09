import NReplay005
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_25204 : CNF.NClause := [(122,true),(31,false),(43,false),(49,false),(55,true),(57,false)]
theorem der_25204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25204 :=
  CNF.rup_sound cl_25204 [cl_3859,cl_25203] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3859 v h) (hints_cons _ _ _ (der_25203 v h) (by intro d hd; cases hd)))
def cl_25205 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,false),(57,false)]
theorem der_25205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25205 :=
  CNF.rup_sound cl_25205 [cl_3861,cl_25197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3861 v h) (hints_cons _ _ _ (der_25197 v h) (by intro d hd; cases hd)))
def cl_25206 : CNF.NClause := [(122,true),(37,true),(43,true),(49,false),(55,true),(57,false)]
theorem der_25206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25206 :=
  CNF.rup_sound cl_25206 [cl_3863,cl_24835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3863 v h) (hints_cons _ _ _ (der_24835 v h) (by intro d hd; cases hd)))
def cl_25207 : CNF.NClause := [(122,true),(37,false),(43,false),(49,true),(55,true),(57,false)]
theorem der_25207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25207 :=
  CNF.rup_sound cl_25207 [cl_3865,cl_3866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3865 v h) (hints_cons _ _ _ (inp_3866 v h) (by intro d hd; cases hd)))
def cl_25208 : CNF.NClause := [(122,true),(37,true),(43,false),(49,true),(55,true),(57,false)]
theorem der_25208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25208 :=
  CNF.rup_sound cl_25208 [cl_3867,cl_24836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3867 v h) (hints_cons _ _ _ (der_24836 v h) (by intro d hd; cases hd)))
def cl_25209 : CNF.NClause := [(122,true),(37,false),(43,true),(49,true),(55,true),(57,false)]
theorem der_25209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25209 :=
  CNF.rup_sound cl_25209 [cl_3869,cl_23810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3869 v h) (hints_cons _ _ _ (der_23810 v h) (by intro d hd; cases hd)))
def cl_25211 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,false),(55,false)]
theorem der_25211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25211 :=
  CNF.rup_sound cl_25211 [cl_3873,cl_3841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3873 v h) (hints_cons _ _ _ (inp_3841 v h) (by intro d hd; cases hd)))
def cl_25212 : CNF.NClause := [(122,true),(37,true),(43,false),(49,false),(55,false),(57,true)]
theorem der_25212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25212 :=
  CNF.rup_sound cl_25212 [cl_3875,cl_24839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3875 v h) (hints_cons _ _ _ (der_24839 v h) (by intro d hd; cases hd)))
def cl_25213 : CNF.NClause := [(122,true),(31,false),(37,false),(43,true),(49,false),(55,false)]
theorem der_25213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25213 :=
  CNF.rup_sound cl_25213 [cl_3877,cl_25197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3877 v h) (hints_cons _ _ _ (der_25197 v h) (by intro d hd; cases hd)))
def cl_25214 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(49,false),(55,false)]
theorem der_25214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25214 :=
  CNF.rup_sound cl_25214 [cl_3879,cl_25198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3879 v h) (hints_cons _ _ _ (der_25198 v h) (by intro d hd; cases hd)))
def cl_25215 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,true),(55,false)]
theorem der_25215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25215 :=
  CNF.rup_sound cl_25215 [cl_3881,cl_25199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3881 v h) (hints_cons _ _ _ (der_25199 v h) (by intro d hd; cases hd)))
def cl_25217 : CNF.NClause := [(122,true),(31,false),(37,false),(49,true),(55,false),(57,true)]
theorem der_25217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25217 :=
  CNF.rup_sound cl_25217 [cl_3885,cl_25215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3885 v h) (hints_cons _ _ _ (der_25215 v h) (by intro d hd; cases hd)))
def cl_25219 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,false),(55,true)]
theorem der_25219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25219 :=
  CNF.rup_sound cl_25219 [cl_3889,cl_25203] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3889 v h) (hints_cons _ _ _ (der_25203 v h) (by intro d hd; cases hd)))
def cl_25220 : CNF.NClause := [(122,true),(37,true),(43,false),(49,false),(55,true),(57,true)]
theorem der_25220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25220 :=
  CNF.rup_sound cl_25220 [cl_3891,cl_24839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3891 v h) (hints_cons _ _ _ (der_24839 v h) (by intro d hd; cases hd)))
def cl_25223 : CNF.NClause := [(122,true),(37,false),(43,false),(49,true),(55,true),(57,true)]
theorem der_25223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25223 :=
  CNF.rup_sound cl_25223 [cl_3897,cl_23781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3897 v h) (hints_cons _ _ _ (der_23781 v h) (by intro d hd; cases hd)))
def cl_25226 : CNF.NClause := [(123,true),(31,false),(41,false),(46,false),(51,false),(56,false)]
theorem der_25226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25226 :=
  CNF.rup_sound cl_25226 [cl_3907,cl_3905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3907 v h) (hints_cons _ _ _ (inp_3905 v h) (by intro d hd; cases hd)))
def cl_25227 : CNF.NClause := [(123,true),(31,false),(36,false),(46,false),(51,false),(56,false)]
theorem der_25227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25227 :=
  CNF.rup_sound cl_25227 [cl_3909,cl_3905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3909 v h) (hints_cons _ _ _ (inp_3905 v h) (by intro d hd; cases hd)))
def cl_25228 : CNF.NClause := [(123,true),(31,false),(36,true),(46,false),(51,false),(56,false)]
theorem der_25228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25228 :=
  CNF.rup_sound cl_25228 [cl_3911,cl_25226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3911 v h) (hints_cons _ _ _ (der_25226 v h) (by intro d hd; cases hd)))
def cl_25229 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(51,false),(56,false)]
theorem der_25229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25229 :=
  CNF.rup_sound cl_25229 [cl_3913,cl_3905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3913 v h) (hints_cons _ _ _ (inp_3905 v h) (by intro d hd; cases hd)))
def cl_25230 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(51,false),(56,false)]
theorem der_25230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25230 :=
  CNF.rup_sound cl_25230 [cl_3915,cl_25226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3915 v h) (hints_cons _ _ _ (der_25226 v h) (by intro d hd; cases hd)))
def cl_25232 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(51,false),(56,false)]
theorem der_25232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25232 :=
  CNF.rup_sound cl_25232 [cl_3919,cl_25228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3919 v h) (hints_cons _ _ _ (der_25228 v h) (by intro d hd; cases hd)))
def cl_25233 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,false),(56,false)]
theorem der_25233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25233 :=
  CNF.rup_sound cl_25233 [cl_3921,cl_3905] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3921 v h) (hints_cons _ _ _ (inp_3905 v h) (by intro d hd; cases hd)))
def cl_25234 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,false),(56,false)]
theorem der_25234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25234 :=
  CNF.rup_sound cl_25234 [cl_3923,cl_25226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3923 v h) (hints_cons _ _ _ (der_25226 v h) (by intro d hd; cases hd)))
def cl_25235 : CNF.NClause := [(123,true),(31,false),(36,false),(41,true),(46,false),(56,false)]
theorem der_25235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25235 :=
  CNF.rup_sound cl_25235 [cl_3925,cl_25227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3925 v h) (hints_cons _ _ _ (der_25227 v h) (by intro d hd; cases hd)))
def cl_25236 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,false),(56,false)]
theorem der_25236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25236 :=
  CNF.rup_sound cl_25236 [cl_3927,cl_25228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3927 v h) (hints_cons _ _ _ (der_25228 v h) (by intro d hd; cases hd)))
def cl_25237 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,true),(56,false)]
theorem der_25237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25237 :=
  CNF.rup_sound cl_25237 [cl_3929,cl_25229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3929 v h) (hints_cons _ _ _ (der_25229 v h) (by intro d hd; cases hd)))
def cl_25241 : CNF.NClause := [(123,true),(36,false),(41,false),(46,false),(51,false),(56,true)]
theorem der_25241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25241 :=
  CNF.rup_sound cl_25241 [cl_3937,cl_23818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3937 v h) (hints_cons _ _ _ (der_23818 v h) (by intro d hd; cases hd)))
def cl_25242 : CNF.NClause := [(123,true),(36,true),(41,false),(46,false),(51,false),(56,true)]
theorem der_25242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25242 :=
  CNF.rup_sound cl_25242 [cl_3939,cl_24910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3939 v h) (hints_cons _ _ _ (der_24910 v h) (by intro d hd; cases hd)))
def cl_25243 : CNF.NClause := [(123,true),(31,false),(36,false),(41,true),(46,false),(51,false)]
theorem der_25243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25243 :=
  CNF.rup_sound cl_25243 [cl_3941,cl_25227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3941 v h) (hints_cons _ _ _ (der_25227 v h) (by intro d hd; cases hd)))
def cl_25244 : CNF.NClause := [(123,true),(36,true),(41,true),(46,false),(51,false),(56,true)]
theorem der_25244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25244 :=
  CNF.rup_sound cl_25244 [cl_3943,cl_3944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3943 v h) (hints_cons _ _ _ (inp_3944 v h) (by intro d hd; cases hd)))
def cl_25245 : CNF.NClause := [(123,true),(36,false),(41,false),(46,true),(51,false),(56,true)]
theorem der_25245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25245 :=
  CNF.rup_sound cl_25245 [cl_3945,cl_3946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3945 v h) (hints_cons _ _ _ (inp_3946 v h) (by intro d hd; cases hd)))
def cl_25246 : CNF.NClause := [(123,true),(31,false),(41,false),(46,true),(51,false),(56,true)]
theorem der_25246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25246 :=
  CNF.rup_sound cl_25246 [cl_3947,cl_25245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3947 v h) (hints_cons _ _ _ (der_25245 v h) (by intro d hd; cases hd)))
def cl_25249 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,false),(56,true)]
theorem der_25249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25249 :=
  CNF.rup_sound cl_25249 [cl_3953,cl_25241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3953 v h) (hints_cons _ _ _ (der_25241 v h) (by intro d hd; cases hd)))
def cl_25250 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,false),(51,true)]
theorem der_25250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25250 :=
  CNF.rup_sound cl_25250 [cl_3955,cl_25234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3955 v h) (hints_cons _ _ _ (der_25234 v h) (by intro d hd; cases hd)))
def cl_25251 : CNF.NClause := [(123,true),(31,false),(36,false),(41,true),(46,false),(51,true)]
theorem der_25251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25251 :=
  CNF.rup_sound cl_25251 [cl_3957,cl_25235] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3957 v h) (hints_cons _ _ _ (der_25235 v h) (by intro d hd; cases hd)))
def cl_25252 : CNF.NClause := [(123,true),(31,false),(36,true),(46,false),(51,true),(56,true)]
theorem der_25252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25252 :=
  CNF.rup_sound cl_25252 [cl_3959,cl_25250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3959 v h) (hints_cons _ _ _ (der_25250 v h) (by intro d hd; cases hd)))
def cl_25253 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,true),(56,true)]
theorem der_25253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25253 :=
  CNF.rup_sound cl_25253 [cl_3961,cl_25245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3961 v h) (hints_cons _ _ _ (der_25245 v h) (by intro d hd; cases hd)))
def cl_25257 : CNF.NClause := [(118,true),(61,false),(32,true),(33,false),(34,false),(35,false)]
theorem der_25257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25257 :=
  CNF.rup_sound cl_25257 [cl_3588,cl_25074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3588 v h) (hints_cons _ _ _ (der_25074 v h) (by intro d hd; cases hd)))
def cl_25258 : CNF.NClause := [(118,true),(61,false),(32,false),(33,true),(34,false),(35,false)]
theorem der_25258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25258 :=
  CNF.rup_sound cl_25258 [cl_3590,cl_25075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3590 v h) (hints_cons _ _ _ (der_25075 v h) (by intro d hd; cases hd)))
def cl_25259 : CNF.NClause := [(118,true),(61,false),(32,true),(33,true),(34,false),(35,false)]
theorem der_25259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25259 :=
  CNF.rup_sound cl_25259 [cl_3592,cl_25076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3592 v h) (hints_cons _ _ _ (der_25076 v h) (by intro d hd; cases hd)))
def cl_25260 : CNF.NClause := [(118,true),(61,false),(32,true),(33,true),(34,true),(35,false)]
theorem der_25260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25260 :=
  CNF.rup_sound cl_25260 [cl_3600,cl_25088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3600 v h) (hints_cons _ _ _ (der_25088 v h) (by intro d hd; cases hd)))
def cl_25261 : CNF.NClause := [(118,true),(61,false),(32,false),(33,false),(34,false),(35,true)]
theorem der_25261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25261 :=
  CNF.rup_sound cl_25261 [cl_3602,cl_25081] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3602 v h) (hints_cons _ _ _ (der_25081 v h) (by intro d hd; cases hd)))
def cl_25262 : CNF.NClause := [(118,true),(61,false),(32,true),(33,false),(34,false),(35,true)]
theorem der_25262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25262 :=
  CNF.rup_sound cl_25262 [cl_3604,cl_25082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3604 v h) (hints_cons _ _ _ (der_25082 v h) (by intro d hd; cases hd)))
def cl_25263 : CNF.NClause := [(118,true),(61,false),(32,false),(34,false),(35,true),(31,true)]
theorem der_25263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25263 :=
  CNF.rup_sound cl_25263 [cl_3606,cl_25261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3606 v h) (hints_cons _ _ _ (der_25261 v h) (by intro d hd; cases hd)))
def cl_25264 : CNF.NClause := [(118,true),(61,false),(32,true),(33,true),(34,false),(35,true)]
theorem der_25264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25264 :=
  CNF.rup_sound cl_25264 [cl_3608,cl_25084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3608 v h) (hints_cons _ _ _ (der_25084 v h) (by intro d hd; cases hd)))
def cl_25265 : CNF.NClause := [(103,true),(61,false),(42,true),(41,false),(44,false),(43,false)]
theorem der_25265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25265 :=
  CNF.rup_sound cl_25265 [cl_2627,cl_2643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2627 v h) (hints_cons _ _ _ (inp_2643 v h) (by intro d hd; cases hd)))
def cl_25266 : CNF.NClause := [(93,true),(61,false),(57,false),(58,false),(59,false),(56,true)]
theorem der_25266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25266 :=
  CNF.rup_sound cl_25266 [cl_1986,cl_2002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1986 v h) (hints_cons _ _ _ (inp_2002 v h) (by intro d hd; cases hd)))
def cl_25267 : CNF.NClause := [(98,true),(61,false),(52,false),(54,false),(55,false),(51,false)]
theorem der_25267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25267 :=
  CNF.rup_sound cl_25267 [cl_2305,cl_2309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2305 v h) (hints_cons _ _ _ (inp_2309 v h) (by intro d hd; cases hd)))
def cl_25268 : CNF.NClause := [(103,true),(61,false),(42,false),(43,false),(45,false),(41,false)]
theorem der_25268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25268 :=
  CNF.rup_sound cl_25268 [cl_2625,cl_2633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2625 v h) (hints_cons _ _ _ (inp_2633 v h) (by intro d hd; cases hd)))
def cl_25269 : CNF.NClause := [(103,true),(61,false),(42,false),(43,true),(45,false),(41,false)]
theorem der_25269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25269 :=
  CNF.rup_sound cl_25269 [cl_2629,cl_23877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2629 v h) (hints_cons _ _ _ (der_23877 v h) (by intro d hd; cases hd)))
def cl_25270 : CNF.NClause := [(103,true),(61,false),(42,true),(43,true),(45,false),(41,false)]
theorem der_25270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25270 :=
  CNF.rup_sound cl_25270 [cl_2631,cl_23877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2631 v h) (hints_cons _ _ _ (der_23877 v h) (by intro d hd; cases hd)))
def cl_25271 : CNF.NClause := [(103,true),(61,false),(43,false),(44,false),(45,true),(41,false)]
theorem der_25271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25271 :=
  CNF.rup_sound cl_25271 [cl_2641,cl_2643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2641 v h) (hints_cons _ _ _ (inp_2643 v h) (by intro d hd; cases hd)))
def cl_25272 : CNF.NClause := [(103,true),(61,false),(42,false),(43,true),(44,false),(41,false)]
theorem der_25272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25272 :=
  CNF.rup_sound cl_25272 [cl_2645,cl_25269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2645 v h) (hints_cons _ _ _ (der_25269 v h) (by intro d hd; cases hd)))
def cl_25273 : CNF.NClause := [(103,true),(61,false),(42,true),(44,false),(45,true),(41,false)]
theorem der_25273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25273 :=
  CNF.rup_sound cl_25273 [cl_2647,cl_2643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2647 v h) (hints_cons _ _ _ (inp_2643 v h) (by intro d hd; cases hd)))
def cl_25274 : CNF.NClause := [(108,true),(61,false),(48,false),(49,false),(50,false),(46,false)]
theorem der_25274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25274 :=
  CNF.rup_sound cl_25274 [cl_2945,cl_2947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2945 v h) (hints_cons _ _ _ (inp_2947 v h) (by intro d hd; cases hd)))
def cl_25275 : CNF.NClause := [(113,true),(37,false),(39,false),(36,false),(38,true),(61,true)]
theorem der_25275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25275 :=
  CNF.rup_sound cl_25275 [cl_3317,cl_23716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3317 v h) (hints_cons _ _ _ (der_23716 v h) (by intro d hd; cases hd)))
def cl_25276 : CNF.NClause := [(113,true),(40,true),(37,false),(39,false),(36,false),(38,false)]
theorem der_25276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25276 :=
  CNF.rup_sound cl_25276 [cl_3313,cl_23675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3313 v h) (hints_cons _ _ _ (der_23675 v h) (by intro d hd; cases hd)))
def cl_25277 : CNF.NClause := [(111,true),(60,true),(55,false),(34,false),(46,false),(42,false)]
theorem der_25277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25277 :=
  CNF.rup_sound cl_25277 [cl_3169,cl_23722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3169 v h) (hints_cons _ _ _ (der_23722 v h) (by intro d hd; cases hd)))
def cl_25278 : CNF.NClause := [(98,true),(61,false),(52,false),(53,false),(51,false),(55,true)]
theorem der_25278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25278 :=
  CNF.rup_sound cl_25278 [cl_2321,cl_25058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2321 v h) (hints_cons _ _ _ (der_25058 v h) (by intro d hd; cases hd)))
def cl_25279 : CNF.NClause := [(94,true),(56,false),(40,false),(50,false),(35,false),(55,true)]
theorem der_25279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25279 :=
  CNF.rup_sound cl_25279 [cl_2065,cl_2069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2065 v h) (hints_cons _ _ _ (inp_2069 v h) (by intro d hd; cases hd)))
def cl_25280 : CNF.NClause := [(115,true),(33,false),(55,true),(44,false),(36,false),(59,false)]
theorem der_25280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25280 :=
  CNF.rup_sound cl_25280 [cl_3409,cl_3417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3409 v h) (hints_cons _ _ _ (inp_3417 v h) (by intro d hd; cases hd)))
def cl_25281 : CNF.NClause := [(115,true),(47,false),(33,false),(44,false),(55,true),(36,false)]
theorem der_25281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25281 :=
  CNF.rup_sound cl_25281 [cl_3441,cl_25280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3441 v h) (hints_cons _ _ _ (der_25280 v h) (by intro d hd; cases hd)))
def cl_25282 : CNF.NClause := [(111,true),(60,false),(38,false),(34,false),(42,false),(55,true)]
theorem der_25282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25282 :=
  CNF.rup_sound cl_25282 [cl_3153,cl_23721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3153 v h) (hints_cons _ _ _ (der_23721 v h) (by intro d hd; cases hd)))
def cl_25283 : CNF.NClause := [(111,true),(60,false),(38,true),(34,false),(46,false),(42,false)]
theorem der_25283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25283 :=
  CNF.rup_sound cl_25283 [cl_3155,cl_3139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3155 v h) (hints_cons _ _ _ (inp_3139 v h) (by intro d hd; cases hd)))
def cl_25284 : CNF.NClause := [(111,true),(34,false),(38,false),(55,true),(42,false),(60,true)]
theorem der_25284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25284 :=
  CNF.rup_sound cl_25284 [cl_3185,cl_23721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3185 v h) (hints_cons _ _ _ (der_23721 v h) (by intro d hd; cases hd)))
def cl_25285 : CNF.NClause := [(111,true),(34,false),(38,true),(46,false),(42,false),(60,true)]
theorem der_25285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25285 :=
  CNF.rup_sound cl_25285 [cl_3187,cl_25277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3187 v h) (hints_cons _ _ _ (der_25277 v h) (by intro d hd; cases hd)))
def cl_25286 : CNF.NClause := [(107,true),(41,false),(32,false),(48,false),(39,false),(58,false)]
theorem der_25286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25286 :=
  CNF.rup_sound cl_25286 [cl_2897,cl_23903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2897 v h) (hints_cons _ _ _ (der_23903 v h) (by intro d hd; cases hd)))
def cl_25287 : CNF.NClause := [(107,true),(41,false),(32,false),(48,false),(39,false),(58,true)]
theorem der_25287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25287 :=
  CNF.rup_sound cl_25287 [cl_2929,cl_25050] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2929 v h) (hints_cons _ _ _ (der_25050 v h) (by intro d hd; cases hd)))
def cl_25288 : CNF.NClause := [(98,true),(51,false),(55,true),(52,false),(53,false),(61,true)]
theorem der_25288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25288 :=
  CNF.rup_sound cl_25288 [cl_2353,cl_25054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2353 v h) (hints_cons _ _ _ (der_25054 v h) (by intro d hd; cases hd)))
def cl_25289 : CNF.NClause := [(122,true),(57,false),(37,false),(31,true),(43,false),(55,true)]
theorem der_25289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25289 :=
  CNF.rup_sound cl_25289 [cl_3858,cl_3866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3858 v h) (hints_cons _ _ _ (inp_3866 v h) (by intro d hd; cases hd)))
def cl_25290 : CNF.NClause := [(122,true),(37,false),(55,true),(31,true),(43,false),(57,true)]
theorem der_25290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25290 :=
  CNF.rup_sound cl_25290 [cl_3890,cl_23781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3890 v h) (hints_cons _ _ _ (der_23781 v h) (by intro d hd; cases hd)))
def cl_25291 : CNF.NClause := [(94,true),(50,false),(40,false),(35,false),(55,true),(56,true)]
theorem der_25291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25291 :=
  CNF.rup_sound cl_25291 [cl_2097,cl_23857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2097 v h) (hints_cons _ _ _ (der_23857 v h) (by intro d hd; cases hd)))
def cl_25292 : CNF.NClause := [(94,true),(56,false),(45,false),(35,false),(50,false),(55,true)]
theorem der_25292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25292 :=
  CNF.rup_sound cl_25292 [cl_2067,cl_25279] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2067 v h) (hints_cons _ _ _ (der_25279 v h) (by intro d hd; cases hd)))
def cl_25293 : CNF.NClause := [(94,true),(50,false),(40,true),(45,false),(35,false),(56,true)]
theorem der_25293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25293 :=
  CNF.rup_sound cl_25293 [cl_2099,cl_23851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2099 v h) (hints_cons _ _ _ (der_23851 v h) (by intro d hd; cases hd)))
def cl_25294 : CNF.NClause := [(108,true),(61,false),(47,false),(48,false),(49,false),(50,false)]
theorem der_25294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25294 :=
  CNF.rup_sound cl_25294 [cl_2946,cl_25274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2946 v h) (hints_cons _ _ _ (der_25274 v h) (by intro d hd; cases hd)))
def cl_25295 : CNF.NClause := [(108,true),(61,false),(47,true),(48,false),(49,false),(50,false)]
theorem der_25295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25295 :=
  CNF.rup_sound cl_25295 [cl_2948,cl_2947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2948 v h) (hints_cons _ _ _ (inp_2947 v h) (by intro d hd; cases hd)))
def cl_25296 : CNF.NClause := [(108,true),(61,false),(47,false),(49,false),(50,false),(46,true)]
theorem der_25296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25296 :=
  CNF.rup_sound cl_25296 [cl_2950,cl_25294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2950 v h) (hints_cons _ _ _ (der_25294 v h) (by intro d hd; cases hd)))
def cl_25297 : CNF.NClause := [(108,true),(61,false),(47,false),(48,false),(49,true),(50,false)]
theorem der_25297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25297 :=
  CNF.rup_sound cl_25297 [cl_2954,cl_23803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2954 v h) (hints_cons _ _ _ (der_23803 v h) (by intro d hd; cases hd)))
def cl_25298 : CNF.NClause := [(108,true),(61,false),(48,true),(49,true),(50,false),(46,true)]
theorem der_25298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25298 :=
  CNF.rup_sound cl_25298 [cl_2958,cl_23853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2958 v h) (hints_cons _ _ _ (der_23853 v h) (by intro d hd; cases hd)))
def cl_25299 : CNF.NClause := [(108,true),(61,false),(47,false),(48,false),(49,false),(46,true)]
theorem der_25299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25299 :=
  CNF.rup_sound cl_25299 [cl_2962,cl_25294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2962 v h) (hints_cons _ _ _ (der_25294 v h) (by intro d hd; cases hd)))
def cl_25300 : CNF.NClause := [(108,true),(61,false),(47,true),(48,false),(49,false),(46,true)]
theorem der_25300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25300 :=
  CNF.rup_sound cl_25300 [cl_2964,cl_25295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2964 v h) (hints_cons _ _ _ (der_25295 v h) (by intro d hd; cases hd)))
def cl_25301 : CNF.NClause := [(108,true),(61,false),(47,false),(48,true),(49,false),(46,true)]
theorem der_25301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25301 :=
  CNF.rup_sound cl_25301 [cl_2966,cl_25296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2966 v h) (hints_cons _ _ _ (der_25296 v h) (by intro d hd; cases hd)))
def cl_25302 : CNF.NClause := [(108,true),(61,false),(47,false),(48,false),(49,true),(46,true)]
theorem der_25302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25302 :=
  CNF.rup_sound cl_25302 [cl_2970,cl_25297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2970 v h) (hints_cons _ _ _ (der_25297 v h) (by intro d hd; cases hd)))
def cl_25304 : CNF.NClause := [(108,true),(61,false),(47,false),(48,true),(49,true),(46,true)]
theorem der_25304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25304 :=
  CNF.rup_sound cl_25304 [cl_2974,cl_25298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2974 v h) (hints_cons _ _ _ (der_25298 v h) (by intro d hd; cases hd)))
def cl_25305 : CNF.NClause := [(108,true),(50,false),(46,true),(47,false),(49,false),(48,false)]
theorem der_25305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25305 :=
  CNF.rup_sound cl_25305 [cl_2978,cl_25294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2978 v h) (hints_cons _ _ _ (der_25294 v h) (by intro d hd; cases hd)))
def cl_25306 : CNF.NClause := [(108,true),(47,false),(46,true),(48,true),(49,false),(50,false)]
theorem der_25306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25306 :=
  CNF.rup_sound cl_25306 [cl_2982,cl_25296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2982 v h) (hints_cons _ _ _ (der_25296 v h) (by intro d hd; cases hd)))
def cl_25307 : CNF.NClause := [(108,true),(49,true),(47,false),(48,false),(46,true),(50,false)]
theorem der_25307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25307 :=
  CNF.rup_sound cl_25307 [cl_2986,cl_25297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2986 v h) (hints_cons _ _ _ (der_25297 v h) (by intro d hd; cases hd)))
def cl_25308 : CNF.NClause := [(108,true),(49,true),(47,false),(48,true),(46,true),(50,false)]
theorem der_25308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25308 :=
  CNF.rup_sound cl_25308 [cl_2990,cl_25298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2990 v h) (hints_cons _ _ _ (der_25298 v h) (by intro d hd; cases hd)))
def cl_25309 : CNF.NClause := [(108,true),(47,false),(50,true),(48,false),(49,false),(46,true)]
theorem der_25309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25309 :=
  CNF.rup_sound cl_25309 [cl_2994,cl_25299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2994 v h) (hints_cons _ _ _ (der_25299 v h) (by intro d hd; cases hd)))
def cl_25310 : CNF.NClause := [(108,true),(47,false),(48,true),(49,false),(46,true),(61,true)]
theorem der_25310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25310 :=
  CNF.rup_sound cl_25310 [cl_2998,cl_25306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2998 v h) (hints_cons _ _ _ (der_25306 v h) (by intro d hd; cases hd)))
def cl_25311 : CNF.NClause := [(108,true),(49,true),(46,true),(48,false),(47,false),(61,true)]
theorem der_25311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25311 :=
  CNF.rup_sound cl_25311 [cl_3002,cl_25307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3002 v h) (hints_cons _ _ _ (der_25307 v h) (by intro d hd; cases hd)))
def cl_25312 : CNF.NClause := [(110,false),(57,true),(39,true),(33,true),(52,true),(46,true)]
theorem der_25312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25312 :=
  CNF.rup_sound cl_25312 [cl_3132,cl_23937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3132 v h) (hints_cons _ _ _ (der_23937 v h) (by intro d hd; cases hd)))
def cl_25313 : CNF.NClause := [(112,true),(54,false),(46,true),(32,false),(43,false),(59,false)]
theorem der_25313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25313 :=
  CNF.rup_sound cl_25313 [cl_3209,cl_3211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3209 v h) (hints_cons _ _ _ (inp_3211 v h) (by intro d hd; cases hd)))
def cl_25314 : CNF.NClause := [(112,true),(43,false),(46,true),(32,false),(54,true),(59,false)]
theorem der_25314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25314 :=
  CNF.rup_sound cl_25314 [cl_3225,cl_23899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3225 v h) (hints_cons _ _ _ (der_23899 v h) (by intro d hd; cases hd)))
def cl_25315 : CNF.NClause := [(112,true),(32,false),(46,true),(59,true),(43,false),(54,true)]
theorem der_25315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25315 :=
  CNF.rup_sound cl_25315 [cl_3257,cl_23900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3257 v h) (hints_cons _ _ _ (der_23900 v h) (by intro d hd; cases hd)))
def cl_25316 : CNF.NClause := [(123,true),(41,false),(31,true),(46,true),(51,false),(56,true)]
theorem der_25316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25316 :=
  CNF.rup_sound cl_25316 [cl_3948,cl_3946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3948 v h) (hints_cons _ _ _ (inp_3946 v h) (by intro d hd; cases hd)))
def cl_25317 : CNF.NClause := [(110,true),(57,false),(33,false),(45,false),(52,true),(39,false)]
theorem der_25317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25317 :=
  CNF.rup_sound cl_25317 [cl_3097,cl_3089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3097 v h) (hints_cons _ _ _ (inp_3089 v h) (by intro d hd; cases hd)))
def cl_25318 : CNF.NClause := [(111,true),(46,true),(42,false),(34,false),(38,false),(60,false)]
theorem der_25318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25318 :=
  CNF.rup_sound cl_25318 [cl_3145,cl_23721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3145 v h) (hints_cons _ _ _ (der_23721 v h) (by intro d hd; cases hd)))
def cl_25319 : CNF.NClause := [(111,true),(46,true),(42,false),(34,false),(38,false),(60,true)]
theorem der_25319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25319 :=
  CNF.rup_sound cl_25319 [cl_3177,cl_23721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3177 v h) (hints_cons _ _ _ (der_23721 v h) (by intro d hd; cases hd)))
def cl_25320 : CNF.NClause := [(100,true),(33,false),(40,false),(49,true),(51,false),(58,false)]
theorem der_25320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25320 :=
  CNF.rup_sound cl_25320 [cl_2445,cl_2441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2445 v h) (hints_cons _ _ _ (inp_2441 v h) (by intro d hd; cases hd)))
def cl_25321 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,false),(58,false)]
theorem der_25321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25321 :=
  CNF.rup_sound cl_25321 [cl_2453,cl_2437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2453 v h) (hints_cons _ _ _ (inp_2437 v h) (by intro d hd; cases hd)))
def cl_25322 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,true),(58,false)]
theorem der_25322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25322 :=
  CNF.rup_sound cl_25322 [cl_2461,cl_25320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2461 v h) (hints_cons _ _ _ (der_25320 v h) (by intro d hd; cases hd)))
def cl_25323 : CNF.NClause := [(100,true),(33,false),(40,false),(49,false),(51,false),(58,true)]
theorem der_25323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25323 :=
  CNF.rup_sound cl_25323 [cl_2469,cl_25042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2469 v h) (hints_cons _ _ _ (der_25042 v h) (by intro d hd; cases hd)))
def cl_25324 : CNF.NClause := [(100,true),(33,false),(40,false),(49,true),(51,false),(58,true)]
theorem der_25324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25324 :=
  CNF.rup_sound cl_25324 [cl_2477,cl_23808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2477 v h) (hints_cons _ _ _ (der_23808 v h) (by intro d hd; cases hd)))
def cl_25325 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,false),(51,true)]
theorem der_25325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25325 :=
  CNF.rup_sound cl_25325 [cl_2485,cl_25321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2485 v h) (hints_cons _ _ _ (der_25321 v h) (by intro d hd; cases hd)))
def cl_25326 : CNF.NClause := [(100,true),(33,false),(40,false),(42,true),(49,true),(51,true)]
theorem der_25326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25326 :=
  CNF.rup_sound cl_25326 [cl_2493,cl_25322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2493 v h) (hints_cons _ _ _ (der_25322 v h) (by intro d hd; cases hd)))
def cl_25327 : CNF.NClause := [(97,true),(32,false),(42,true),(47,false),(52,false),(56,false)]
theorem der_25327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25327 :=
  CNF.rup_sound cl_25327 [cl_2245,cl_24775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2245 v h) (hints_cons _ _ _ (der_24775 v h) (by intro d hd; cases hd)))
def cl_25328 : CNF.NClause := [(97,true),(32,false),(42,true),(47,true),(52,false),(56,false)]
theorem der_25328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25328 :=
  CNF.rup_sound cl_25328 [cl_2253,cl_24777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2253 v h) (hints_cons _ _ _ (der_24777 v h) (by intro d hd; cases hd)))
def cl_25329 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,false),(56,false)]
theorem der_25329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25329 :=
  CNF.rup_sound cl_25329 [cl_2261,cl_25327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2261 v h) (hints_cons _ _ _ (der_25327 v h) (by intro d hd; cases hd)))
def cl_25331 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,false),(45,false)]
theorem der_25331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25331 :=
  CNF.rup_sound cl_25331 [cl_2663,cl_25270] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2663 v h) (hints_cons _ _ _ (der_25270 v h) (by intro d hd; cases hd)))
def cl_25332 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,false),(45,true)]
theorem der_25332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25332 :=
  CNF.rup_sound cl_25332 [cl_2679,cl_25273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2679 v h) (hints_cons _ _ _ (der_25273 v h) (by intro d hd; cases hd)))
def cl_25333 : CNF.NClause := [(103,true),(41,false),(43,false),(44,true),(45,true),(61,true)]
theorem der_25333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25333 :=
  CNF.rup_sound cl_25333 [cl_2683,cl_2681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2683 v h) (hints_cons _ _ _ (inp_2681 v h) (by intro d hd; cases hd)))
def cl_25334 : CNF.NClause := [(111,true),(34,false),(42,true),(46,false),(55,false),(60,false)]
theorem der_25334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25334 :=
  CNF.rup_sound cl_25334 [cl_3141,cl_23718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3141 v h) (hints_cons _ _ _ (der_23718 v h) (by intro d hd; cases hd)))
def cl_25335 : CNF.NClause := [(111,true),(34,false),(38,false),(46,true),(55,false),(60,false)]
theorem der_25335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25335 :=
  CNF.rup_sound cl_25335 [cl_3149,cl_25318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3149 v h) (hints_cons _ _ _ (der_25318 v h) (by intro d hd; cases hd)))
def cl_25336 : CNF.NClause := [(111,true),(34,false),(38,false),(46,false),(55,true),(60,false)]
theorem der_25336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25336 :=
  CNF.rup_sound cl_25336 [cl_3157,cl_25282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3157 v h) (hints_cons _ _ _ (der_25282 v h) (by intro d hd; cases hd)))
def cl_25337 : CNF.NClause := [(111,true),(34,false),(38,false),(46,true),(55,true),(60,false)]
theorem der_25337 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25337 :=
  CNF.rup_sound cl_25337 [cl_3165,cl_23721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3165 v h) (hints_cons _ _ _ (der_23721 v h) (by intro d hd; cases hd)))
def cl_25338 : CNF.NClause := [(111,true),(34,false),(38,false),(46,false),(55,false),(60,true)]
theorem der_25338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25338 :=
  CNF.rup_sound cl_25338 [cl_3173,cl_25277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3173 v h) (hints_cons _ _ _ (der_25277 v h) (by intro d hd; cases hd)))
def cl_25339 : CNF.NClause := [(111,true),(34,false),(38,false),(46,true),(55,false),(60,true)]
theorem der_25339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25339 :=
  CNF.rup_sound cl_25339 [cl_3181,cl_25319] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3181 v h) (hints_cons _ _ _ (der_25319 v h) (by intro d hd; cases hd)))
def cl_25340 : CNF.NClause := [(111,true),(34,false),(38,false),(46,false),(55,true),(60,true)]
theorem der_25340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25340 :=
  CNF.rup_sound cl_25340 [cl_3189,cl_25284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3189 v h) (hints_cons _ _ _ (der_25284 v h) (by intro d hd; cases hd)))
def cl_25341 : CNF.NClause := [(111,true),(34,false),(38,false),(46,true),(55,true),(60,true)]
theorem der_25341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25341 :=
  CNF.rup_sound cl_25341 [cl_3197,cl_23721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3197 v h) (hints_cons _ _ _ (der_23721 v h) (by intro d hd; cases hd)))
def cl_25342 : CNF.NClause := [(114,true),(57,false),(35,false),(48,false),(54,false),(36,false)]
theorem der_25342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25342 :=
  CNF.rup_sound cl_25342 [cl_3333,cl_23840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3333 v h) (hints_cons _ _ _ (der_23840 v h) (by intro d hd; cases hd)))
def cl_25343 : CNF.NClause := [(114,true),(57,false),(35,false),(48,true),(54,false),(36,false)]
theorem der_25343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25343 :=
  CNF.rup_sound cl_25343 [cl_3341,cl_3337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3341 v h) (hints_cons _ _ _ (inp_3337 v h) (by intro d hd; cases hd)))
def cl_25344 : CNF.NClause := [(114,true),(35,false),(42,true),(48,false),(36,false),(57,false)]
theorem der_25344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25344 :=
  CNF.rup_sound cl_25344 [cl_3349,cl_25342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3349 v h) (hints_cons _ _ _ (der_25342 v h) (by intro d hd; cases hd)))
def cl_25345 : CNF.NClause := [(114,true),(35,false),(42,true),(48,true),(36,false),(57,false)]
theorem der_25345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25345 :=
  CNF.rup_sound cl_25345 [cl_3357,cl_25343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3357 v h) (hints_cons _ _ _ (der_25343 v h) (by intro d hd; cases hd)))
def cl_25346 : CNF.NClause := [(114,true),(42,true),(35,false),(36,false),(48,false),(54,false)]
theorem der_25346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25346 :=
  CNF.rup_sound cl_25346 [cl_3365,cl_25342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3365 v h) (hints_cons _ _ _ (der_25342 v h) (by intro d hd; cases hd)))
def cl_25347 : CNF.NClause := [(114,true),(48,true),(35,false),(42,true),(36,false),(54,false)]
theorem der_25347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25347 :=
  CNF.rup_sound cl_25347 [cl_3373,cl_25343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3373 v h) (hints_cons _ _ _ (der_25343 v h) (by intro d hd; cases hd)))
def cl_25348 : CNF.NClause := [(114,true),(54,true),(35,false),(48,false),(36,false),(57,true)]
theorem der_25348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25348 :=
  CNF.rup_sound cl_25348 [cl_3381,cl_25065] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3381 v h) (hints_cons _ _ _ (der_25065 v h) (by intro d hd; cases hd)))
def cl_25349 : CNF.NClause := [(114,true),(54,true),(35,false),(42,true),(48,true),(36,false)]
theorem der_25349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25349 :=
  CNF.rup_sound cl_25349 [cl_3389,cl_25345] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3389 v h) (hints_cons _ _ _ (der_25345 v h) (by intro d hd; cases hd)))
def cl_25350 : CNF.NClause := [(121,true),(59,false),(31,true),(50,false),(53,false),(39,false)]
theorem der_25350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25350 :=
  CNF.rup_sound cl_25350 [cl_3782,cl_23792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3782 v h) (hints_cons _ _ _ (der_23792 v h) (by intro d hd; cases hd)))
def cl_25351 : CNF.NClause := [(121,true),(59,false),(53,false),(31,true),(50,true),(42,true)]
theorem der_25351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25351 :=
  CNF.rup_sound cl_25351 [cl_3790,cl_3792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3790 v h) (hints_cons _ _ _ (inp_3792 v h) (by intro d hd; cases hd)))
def cl_25352 : CNF.NClause := [(121,true),(53,true),(31,true),(50,false),(39,false),(59,false)]
theorem der_25352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25352 :=
  CNF.rup_sound cl_25352 [cl_3798,cl_3794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3798 v h) (hints_cons _ _ _ (inp_3794 v h) (by intro d hd; cases hd)))
def cl_25353 : CNF.NClause := [(121,true),(53,true),(39,false),(31,true),(42,true),(59,false)]
theorem der_25353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25353 :=
  CNF.rup_sound cl_25353 [cl_3806,cl_25352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3806 v h) (hints_cons _ _ _ (der_25352 v h) (by intro d hd; cases hd)))
def cl_25354 : CNF.NClause := [(121,true),(50,false),(42,true),(39,false),(53,false),(59,true)]
theorem der_25354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25354 :=
  CNF.rup_sound cl_25354 [cl_3814,cl_25183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3814 v h) (hints_cons _ _ _ (der_25183 v h) (by intro d hd; cases hd)))
def cl_25355 : CNF.NClause := [(121,true),(42,true),(53,false),(50,true),(39,false),(59,true)]
theorem der_25355 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25355 :=
  CNF.rup_sound cl_25355 [cl_3822,cl_25187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3822 v h) (hints_cons _ _ _ (der_25187 v h) (by intro d hd; cases hd)))
def cl_25356 : CNF.NClause := [(121,true),(50,false),(31,true),(39,false),(53,true),(59,true)]
theorem der_25356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25356 :=
  CNF.rup_sound cl_25356 [cl_3830,cl_23744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3830 v h) (hints_cons _ _ _ (der_23744 v h) (by intro d hd; cases hd)))
def cl_25357 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,false),(45,false)]
theorem der_25357 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25357 :=
  CNF.rup_sound cl_25357 [cl_2659,cl_25265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2659 v h) (hints_cons _ _ _ (der_25265 v h) (by intro d hd; cases hd)))
def cl_25358 : CNF.NClause := [(100,true),(33,false),(42,true),(49,false),(51,false),(58,false)]
theorem der_25358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25358 :=
  CNF.rup_sound cl_25358 [cl_2439,cl_2437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2439 v h) (hints_cons _ _ _ (inp_2437 v h) (by intro d hd; cases hd)))
def cl_25359 : CNF.NClause := [(100,true),(33,false),(40,true),(49,true),(51,false),(58,false)]
theorem der_25359 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25359 :=
  CNF.rup_sound cl_25359 [cl_2447,cl_23814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2447 v h) (hints_cons _ _ _ (der_23814 v h) (by intro d hd; cases hd)))
def cl_25360 : CNF.NClause := [(100,true),(33,false),(42,true),(49,false),(51,true),(58,false)]
theorem der_25360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25360 :=
  CNF.rup_sound cl_25360 [cl_2455,cl_25321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2455 v h) (hints_cons _ _ _ (der_25321 v h) (by intro d hd; cases hd)))
def cl_25361 : CNF.NClause := [(100,true),(33,false),(42,true),(49,true),(51,true),(58,false)]
theorem der_25361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25361 :=
  CNF.rup_sound cl_25361 [cl_2463,cl_25322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2463 v h) (hints_cons _ _ _ (der_25322 v h) (by intro d hd; cases hd)))
def cl_25362 : CNF.NClause := [(100,true),(33,false),(40,true),(49,false),(51,false),(58,true)]
theorem der_25362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25362 :=
  CNF.rup_sound cl_25362 [cl_2471,cl_25043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2471 v h) (hints_cons _ _ _ (der_25043 v h) (by intro d hd; cases hd)))
def cl_25363 : CNF.NClause := [(100,true),(33,false),(42,true),(49,true),(51,false),(58,true)]
theorem der_25363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25363 :=
  CNF.rup_sound cl_25363 [cl_2479,cl_25324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2479 v h) (hints_cons _ _ _ (der_25324 v h) (by intro d hd; cases hd)))
def cl_25364 : CNF.NClause := [(100,true),(33,false),(42,true),(49,false),(51,true),(58,true)]
theorem der_25364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25364 :=
  CNF.rup_sound cl_25364 [cl_2487,cl_25325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2487 v h) (hints_cons _ _ _ (der_25325 v h) (by intro d hd; cases hd)))
def cl_25365 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,false),(52,false)]
theorem der_25365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25365 :=
  CNF.rup_sound cl_25365 [cl_2277,cl_25327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2277 v h) (hints_cons _ _ _ (der_25327 v h) (by intro d hd; cases hd)))
def cl_25366 : CNF.NClause := [(97,true),(32,false),(37,false),(42,true),(47,true),(52,false)]
theorem der_25366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25366 :=
  CNF.rup_sound cl_25366 [cl_2285,cl_25328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2285 v h) (hints_cons _ _ _ (der_25328 v h) (by intro d hd; cases hd)))
def cl_25367 : CNF.NClause := [(97,true),(32,false),(37,false),(47,false),(52,true),(56,true)]
theorem der_25367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25367 :=
  CNF.rup_sound cl_25367 [cl_2293,cl_2289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2293 v h) (hints_cons _ _ _ (inp_2289 v h) (by intro d hd; cases hd)))
def cl_25368 : CNF.NClause := [(97,true),(32,false),(37,false),(47,true),(52,true),(56,true)]
theorem der_25368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25368 :=
  CNF.rup_sound cl_25368 [cl_2301,cl_23798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2301 v h) (hints_cons _ _ _ (der_23798 v h) (by intro d hd; cases hd)))
def cl_25369 : CNF.NClause := [(111,true),(55,false),(46,false),(38,true),(34,false),(60,true)]
theorem der_25369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25369 :=
  CNF.rup_sound cl_25369 [cl_3175,cl_25277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3175 v h) (hints_cons _ _ _ (der_25277 v h) (by intro d hd; cases hd)))
def cl_25370 : CNF.NClause := [(111,true),(34,false),(42,true),(38,true),(46,true),(55,false)]
theorem der_25370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25370 :=
  CNF.rup_sound cl_25370 [cl_3183,cl_23724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3183 v h) (hints_cons _ _ _ (der_23724 v h) (by intro d hd; cases hd)))
def cl_25371 : CNF.NClause := [(96,true),(56,false),(44,false),(49,false),(54,false),(34,true)]
theorem der_25371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25371 :=
  CNF.rup_sound cl_25371 [cl_2180,cl_2178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2180 v h) (hints_cons _ _ _ (inp_2178 v h) (by intro d hd; cases hd)))
def cl_25372 : CNF.NClause := [(96,true),(34,true),(39,false),(49,false),(54,false),(56,false)]
theorem der_25372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25372 :=
  CNF.rup_sound cl_25372 [cl_2182,cl_2178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2182 v h) (hints_cons _ _ _ (inp_2178 v h) (by intro d hd; cases hd)))
def cl_25373 : CNF.NClause := [(96,true),(56,false),(39,true),(49,false),(54,false),(34,true)]
theorem der_25373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25373 :=
  CNF.rup_sound cl_25373 [cl_2184,cl_25371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2184 v h) (hints_cons _ _ _ (der_25371 v h) (by intro d hd; cases hd)))
def cl_25374 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(54,false),(56,false)]
theorem der_25374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25374 :=
  CNF.rup_sound cl_25374 [cl_2186,cl_2178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2186 v h) (hints_cons _ _ _ (inp_2178 v h) (by intro d hd; cases hd)))
def cl_25375 : CNF.NClause := [(96,true),(56,false),(39,true),(44,false),(54,false),(34,true)]
theorem der_25375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25375 :=
  CNF.rup_sound cl_25375 [cl_2188,cl_25371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2188 v h) (hints_cons _ _ _ (der_25371 v h) (by intro d hd; cases hd)))
def cl_25376 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(54,false),(56,false)]
theorem der_25376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25376 :=
  CNF.rup_sound cl_25376 [cl_2190,cl_25372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2190 v h) (hints_cons _ _ _ (der_25372 v h) (by intro d hd; cases hd)))
def cl_25378 : CNF.NClause := [(96,true),(34,true),(39,false),(44,false),(49,false),(56,false)]
theorem der_25378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25378 :=
  CNF.rup_sound cl_25378 [cl_2194,cl_2178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2194 v h) (hints_cons _ _ _ (inp_2178 v h) (by intro d hd; cases hd)))
def cl_25380 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,false),(56,false)]
theorem der_25380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25380 :=
  CNF.rup_sound cl_25380 [cl_2198,cl_25372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2198 v h) (hints_cons _ _ _ (der_25372 v h) (by intro d hd; cases hd)))
def cl_25382 : CNF.NClause := [(96,true),(39,false),(44,false),(49,true),(54,true),(56,false)]
theorem der_25382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25382 :=
  CNF.rup_sound cl_25382 [cl_2202,cl_2201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2202 v h) (hints_cons _ _ _ (inp_2201 v h) (by intro d hd; cases hd)))
def cl_25383 : CNF.NClause := [(96,true),(56,false),(39,true),(44,false),(49,true),(54,true)]
theorem der_25383 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25383 :=
  CNF.rup_sound cl_25383 [cl_2204,cl_23807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2204 v h) (hints_cons _ _ _ (der_23807 v h) (by intro d hd; cases hd)))
def cl_25384 : CNF.NClause := [(96,true),(34,true),(39,false),(44,true),(49,true),(56,false)]
theorem der_25384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25384 :=
  CNF.rup_sound cl_25384 [cl_2206,cl_25376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2206 v h) (hints_cons _ _ _ (der_25376 v h) (by intro d hd; cases hd)))
def cl_25385 : CNF.NClause := [(96,true),(49,false),(39,false),(44,false),(34,true),(54,false)]
theorem der_25385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25385 :=
  CNF.rup_sound cl_25385 [cl_2210,cl_2178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2210 v h) (hints_cons _ _ _ (inp_2178 v h) (by intro d hd; cases hd)))
def cl_25386 : CNF.NClause := [(96,true),(54,false),(39,true),(44,false),(49,false),(56,true)]
theorem der_25386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25386 :=
  CNF.rup_sound cl_25386 [cl_2212,cl_24752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2212 v h) (hints_cons _ _ _ (der_24752 v h) (by intro d hd; cases hd)))
def cl_25387 : CNF.NClause := [(96,true),(49,false),(39,false),(44,true),(34,true),(54,false)]
theorem der_25387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25387 :=
  CNF.rup_sound cl_25387 [cl_2214,cl_25372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2214 v h) (hints_cons _ _ _ (der_25372 v h) (by intro d hd; cases hd)))
def cl_25388 : CNF.NClause := [(96,true),(49,false),(39,true),(44,true),(54,false),(34,true)]
theorem der_25388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25388 :=
  CNF.rup_sound cl_25388 [cl_2216,cl_25373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2216 v h) (hints_cons _ _ _ (der_25373 v h) (by intro d hd; cases hd)))
def cl_25389 : CNF.NClause := [(96,true),(49,true),(39,false),(44,false),(34,true),(54,false)]
theorem der_25389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25389 :=
  CNF.rup_sound cl_25389 [cl_2218,cl_25374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2218 v h) (hints_cons _ _ _ (der_25374 v h) (by intro d hd; cases hd)))
def cl_25390 : CNF.NClause := [(96,true),(39,true),(44,false),(54,false),(49,true),(56,true)]
theorem der_25390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25390 :=
  CNF.rup_sound cl_25390 [cl_2220,cl_24752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2220 v h) (hints_cons _ _ _ (der_24752 v h) (by intro d hd; cases hd)))
def cl_25391 : CNF.NClause := [(96,true),(49,true),(39,false),(44,true),(34,true),(54,false)]
theorem der_25391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25391 :=
  CNF.rup_sound cl_25391 [cl_2222,cl_25376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2222 v h) (hints_cons _ _ _ (der_25376 v h) (by intro d hd; cases hd)))
def cl_25392 : CNF.NClause := [(96,true),(54,true),(39,false),(44,false),(49,false),(56,true)]
theorem der_25392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25392 :=
  CNF.rup_sound cl_25392 [cl_2226,cl_25063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2226 v h) (hints_cons _ _ _ (der_25063 v h) (by intro d hd; cases hd)))
def cl_25393 : CNF.NClause := [(96,true),(54,true),(39,true),(44,false),(49,false),(56,true)]
theorem der_25393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25393 :=
  CNF.rup_sound cl_25393 [cl_2228,cl_24753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2228 v h) (hints_cons _ _ _ (der_24753 v h) (by intro d hd; cases hd)))
def cl_25394 : CNF.NClause := [(96,true),(39,false),(34,true),(44,true),(49,false),(54,true)]
theorem der_25394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25394 :=
  CNF.rup_sound cl_25394 [cl_2230,cl_25380] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2230 v h) (hints_cons _ _ _ (der_25380 v h) (by intro d hd; cases hd)))
def cl_25395 : CNF.NClause := [(96,true),(39,false),(44,false),(49,true),(54,true),(56,true)]
theorem der_25395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25395 :=
  CNF.rup_sound cl_25395 [cl_2234,cl_23809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2234 v h) (hints_cons _ _ _ (der_23809 v h) (by intro d hd; cases hd)))
def cl_25396 : CNF.NClause := [(101,true),(51,false),(37,false),(45,false),(48,false),(59,false)]
theorem der_25396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25396 :=
  CNF.rup_sound cl_25396 [cl_2498,cl_23848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2498 v h) (hints_cons _ _ _ (der_23848 v h) (by intro d hd; cases hd)))
def cl_25397 : CNF.NClause := [(101,true),(51,false),(45,false),(48,false),(37,true),(59,false)]
theorem der_25397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25397 :=
  CNF.rup_sound cl_25397 [cl_2500,cl_24803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2500 v h) (hints_cons _ _ _ (der_24803 v h) (by intro d hd; cases hd)))
def cl_25398 : CNF.NClause := [(101,true),(51,false),(37,false),(45,true),(48,false),(59,false)]
theorem der_25398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25398 :=
  CNF.rup_sound cl_25398 [cl_2502,cl_23847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2502 v h) (hints_cons _ _ _ (der_23847 v h) (by intro d hd; cases hd)))
def cl_25399 : CNF.NClause := [(101,true),(51,false),(37,true),(48,false),(45,true),(59,false)]
theorem der_25399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25399 :=
  CNF.rup_sound cl_25399 [cl_2504,cl_24804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2504 v h) (hints_cons _ _ _ (der_24804 v h) (by intro d hd; cases hd)))
def cl_25400 : CNF.NClause := [(101,true),(51,false),(37,false),(45,false),(34,true),(59,false)]
theorem der_25400 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25400 :=
  CNF.rup_sound cl_25400 [cl_2506,cl_25396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2506 v h) (hints_cons _ _ _ (der_25396 v h) (by intro d hd; cases hd)))
def cl_25401 : CNF.NClause := [(101,true),(51,false),(34,true),(45,false),(37,true),(59,false)]
theorem der_25401 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25401 :=
  CNF.rup_sound cl_25401 [cl_2508,cl_25397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2508 v h) (hints_cons _ _ _ (der_25397 v h) (by intro d hd; cases hd)))
def cl_25402 : CNF.NClause := [(101,true),(51,false),(37,false),(45,true),(48,true),(59,false)]
theorem der_25402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25402 :=
  CNF.rup_sound cl_25402 [cl_2510,cl_2509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2510 v h) (hints_cons _ _ _ (inp_2509 v h) (by intro d hd; cases hd)))
def cl_25403 : CNF.NClause := [(101,true),(51,false),(37,true),(48,true),(45,true),(59,false)]
theorem der_25403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25403 :=
  CNF.rup_sound cl_25403 [cl_2512,cl_24806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2512 v h) (hints_cons _ _ _ (der_24806 v h) (by intro d hd; cases hd)))
def cl_25404 : CNF.NClause := [(101,true),(59,false),(37,false),(45,false),(48,false),(34,true)]
theorem der_25404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25404 :=
  CNF.rup_sound cl_25404 [cl_2514,cl_25396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2514 v h) (hints_cons _ _ _ (der_25396 v h) (by intro d hd; cases hd)))
def cl_25405 : CNF.NClause := [(101,true),(48,false),(34,true),(45,false),(37,true),(59,false)]
theorem der_25405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25405 :=
  CNF.rup_sound cl_25405 [cl_2516,cl_25397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2516 v h) (hints_cons _ _ _ (der_25397 v h) (by intro d hd; cases hd)))
def cl_25406 : CNF.NClause := [(101,true),(59,false),(37,false),(45,true),(48,false),(34,true)]
theorem der_25406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25406 :=
  CNF.rup_sound cl_25406 [cl_2518,cl_25398] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2518 v h) (hints_cons _ _ _ (der_25398 v h) (by intro d hd; cases hd)))
def cl_25407 : CNF.NClause := [(101,true),(59,false),(37,true),(48,false),(51,true),(45,true)]
theorem der_25407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25407 :=
  CNF.rup_sound cl_25407 [cl_2520,cl_24808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2520 v h) (hints_cons _ _ _ (der_24808 v h) (by intro d hd; cases hd)))
def cl_25408 : CNF.NClause := [(101,true),(59,false),(37,false),(45,false),(48,true),(34,true)]
theorem der_25408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25408 :=
  CNF.rup_sound cl_25408 [cl_2522,cl_25400] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2522 v h) (hints_cons _ _ _ (der_25400 v h) (by intro d hd; cases hd)))
def cl_25409 : CNF.NClause := [(101,true),(59,false),(45,false),(48,true),(51,true),(37,true)]
theorem der_25409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25409 :=
  CNF.rup_sound cl_25409 [cl_2524,cl_24809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2524 v h) (hints_cons _ _ _ (der_24809 v h) (by intro d hd; cases hd)))
def cl_25410 : CNF.NClause := [(101,true),(59,false),(37,false),(45,true),(48,true),(34,true)]
theorem der_25410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25410 :=
  CNF.rup_sound cl_25410 [cl_2526,cl_25402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2526 v h) (hints_cons _ _ _ (der_25402 v h) (by intro d hd; cases hd)))
def cl_25411 : CNF.NClause := [(101,true),(51,false),(37,false),(45,false),(48,false),(34,true)]
theorem der_25411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25411 :=
  CNF.rup_sound cl_25411 [cl_2530,cl_25396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2530 v h) (hints_cons _ _ _ (der_25396 v h) (by intro d hd; cases hd)))
def cl_25412 : CNF.NClause := [(101,true),(51,false),(37,true),(48,false),(34,true),(45,false)]
theorem der_25412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25412 :=
  CNF.rup_sound cl_25412 [cl_2532,cl_25397] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2532 v h) (hints_cons _ _ _ (der_25397 v h) (by intro d hd; cases hd)))
def cl_25413 : CNF.NClause := [(101,true),(51,false),(37,false),(45,true),(48,false),(34,true)]
theorem der_25413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25413 :=
  CNF.rup_sound cl_25413 [cl_2534,cl_25398] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2534 v h) (hints_cons _ _ _ (der_25398 v h) (by intro d hd; cases hd)))
def cl_25414 : CNF.NClause := [(101,true),(51,false),(37,true),(34,true),(48,false),(45,true)]
theorem der_25414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25414 :=
  CNF.rup_sound cl_25414 [cl_2536,cl_25399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2536 v h) (hints_cons _ _ _ (der_25399 v h) (by intro d hd; cases hd)))
def cl_25415 : CNF.NClause := [(101,true),(51,false),(37,false),(45,false),(48,true),(34,true)]
theorem der_25415 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25415 :=
  CNF.rup_sound cl_25415 [cl_2538,cl_25400] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2538 v h) (hints_cons _ _ _ (der_25400 v h) (by intro d hd; cases hd)))
def cl_25416 : CNF.NClause := [(101,true),(37,true),(45,false),(51,false),(34,true),(59,true)]
theorem der_25416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25416 :=
  CNF.rup_sound cl_25416 [cl_2540,cl_25412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2540 v h) (hints_cons _ _ _ (der_25412 v h) (by intro d hd; cases hd)))
def cl_25417 : CNF.NClause := [(101,true),(51,false),(37,false),(45,true),(48,true),(34,true)]
theorem der_25417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25417 :=
  CNF.rup_sound cl_25417 [cl_2542,cl_25402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2542 v h) (hints_cons _ _ _ (der_25402 v h) (by intro d hd; cases hd)))
def cl_25418 : CNF.NClause := [(101,true),(48,false),(37,false),(45,false),(34,true),(59,true)]
theorem der_25418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25418 :=
  CNF.rup_sound cl_25418 [cl_2546,cl_25411] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2546 v h) (hints_cons _ _ _ (der_25411 v h) (by intro d hd; cases hd)))
def cl_25419 : CNF.NClause := [(101,true),(48,false),(37,true),(45,false),(34,true),(51,true)]
theorem der_25419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25419 :=
  CNF.rup_sound cl_25419 [cl_2548,cl_25405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2548 v h) (hints_cons _ _ _ (der_25405 v h) (by intro d hd; cases hd)))
def cl_25420 : CNF.NClause := [(101,true),(48,false),(37,false),(45,true),(34,true),(59,true)]
theorem der_25420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25420 :=
  CNF.rup_sound cl_25420 [cl_2550,cl_25413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2550 v h) (hints_cons _ _ _ (der_25413 v h) (by intro d hd; cases hd)))
def cl_25421 : CNF.NClause := [(101,true),(37,false),(34,true),(45,false),(48,true),(51,true)]
theorem der_25421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25421 :=
  CNF.rup_sound cl_25421 [cl_2554,cl_25408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2554 v h) (hints_cons _ _ _ (der_25408 v h) (by intro d hd; cases hd)))
def cl_25422 : CNF.NClause := [(106,true),(47,false),(41,false),(40,false),(53,false),(57,false)]
theorem der_25422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25422 :=
  CNF.rup_sound cl_25422 [cl_2818,cl_2817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2818 v h) (hints_cons _ _ _ (inp_2817 v h) (by intro d hd; cases hd)))
def cl_25423 : CNF.NClause := [(106,true),(41,false),(34,true),(47,false),(53,false),(57,false)]
theorem der_25423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25423 :=
  CNF.rup_sound cl_25423 [cl_2820,cl_25422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2820 v h) (hints_cons _ _ _ (der_25422 v h) (by intro d hd; cases hd)))
def cl_25424 : CNF.NClause := [(106,true),(47,false),(34,true),(40,false),(53,false),(57,false)]
theorem der_25424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25424 :=
  CNF.rup_sound cl_25424 [cl_2822,cl_25422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2822 v h) (hints_cons _ _ _ (der_25422 v h) (by intro d hd; cases hd)))
def cl_25425 : CNF.NClause := [(106,true),(53,false),(40,true),(34,true),(47,false),(57,false)]
theorem der_25425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25425 :=
  CNF.rup_sound cl_25425 [cl_2824,cl_25423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2824 v h) (hints_cons _ _ _ (der_25423 v h) (by intro d hd; cases hd)))
def cl_25426 : CNF.NClause := [(106,true),(41,false),(34,true),(40,false),(53,false),(57,false)]
theorem der_25426 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25426 :=
  CNF.rup_sound cl_25426 [cl_2826,cl_25422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2826 v h) (hints_cons _ _ _ (der_25422 v h) (by intro d hd; cases hd)))
def cl_25427 : CNF.NClause := [(106,true),(41,false),(40,true),(34,true),(53,false),(57,false)]
theorem der_25427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25427 :=
  CNF.rup_sound cl_25427 [cl_2828,cl_25423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2828 v h) (hints_cons _ _ _ (der_25423 v h) (by intro d hd; cases hd)))
def cl_25428 : CNF.NClause := [(106,true),(57,false),(34,true),(41,true),(53,false),(40,false)]
theorem der_25428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25428 :=
  CNF.rup_sound cl_25428 [cl_2830,cl_25424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2830 v h) (hints_cons _ _ _ (der_25424 v h) (by intro d hd; cases hd)))
def cl_25429 : CNF.NClause := [(106,true),(40,true),(41,true),(34,true),(53,false),(57,false)]
theorem der_25429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25429 :=
  CNF.rup_sound cl_25429 [cl_2832,cl_25425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2832 v h) (hints_cons _ _ _ (der_25425 v h) (by intro d hd; cases hd)))
def cl_25430 : CNF.NClause := [(106,true),(47,false),(41,false),(40,false),(53,true),(57,false)]
theorem der_25430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25430 :=
  CNF.rup_sound cl_25430 [cl_2834,cl_23737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2834 v h) (hints_cons _ _ _ (der_23737 v h) (by intro d hd; cases hd)))
def cl_25431 : CNF.NClause := [(106,true),(41,false),(40,true),(47,false),(53,true),(57,false)]
theorem der_25431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25431 :=
  CNF.rup_sound cl_25431 [cl_2836,cl_23737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2836 v h) (hints_cons _ _ _ (der_23737 v h) (by intro d hd; cases hd)))
def cl_25432 : CNF.NClause := [(106,true),(47,false),(34,true),(41,true),(40,false),(57,false)]
theorem der_25432 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25432 :=
  CNF.rup_sound cl_25432 [cl_2838,cl_25424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2838 v h) (hints_cons _ _ _ (der_25424 v h) (by intro d hd; cases hd)))
def cl_25433 : CNF.NClause := [(106,true),(40,true),(47,false),(41,true),(34,true),(57,false)]
theorem der_25433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25433 :=
  CNF.rup_sound cl_25433 [cl_2840,cl_25425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2840 v h) (hints_cons _ _ _ (der_25425 v h) (by intro d hd; cases hd)))
def cl_25434 : CNF.NClause := [(106,true),(41,false),(40,false),(47,true),(53,true),(57,false)]
theorem der_25434 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25434 :=
  CNF.rup_sound cl_25434 [cl_2842,cl_23750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2842 v h) (hints_cons _ _ _ (der_23750 v h) (by intro d hd; cases hd)))
def cl_25435 : CNF.NClause := [(106,true),(41,false),(40,true),(34,true),(47,true),(57,false)]
theorem der_25435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25435 :=
  CNF.rup_sound cl_25435 [cl_2844,cl_25427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2844 v h) (hints_cons _ _ _ (der_25427 v h) (by intro d hd; cases hd)))
def cl_25436 : CNF.NClause := [(106,true),(57,false),(34,true),(41,true),(47,true),(40,false)]
theorem der_25436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25436 :=
  CNF.rup_sound cl_25436 [cl_2846,cl_25428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2846 v h) (hints_cons _ _ _ (der_25428 v h) (by intro d hd; cases hd)))
def cl_25437 : CNF.NClause := [(106,true),(47,false),(34,true),(41,false),(40,false),(53,false)]
theorem der_25437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25437 :=
  CNF.rup_sound cl_25437 [cl_2850,cl_25422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2850 v h) (hints_cons _ _ _ (der_25422 v h) (by intro d hd; cases hd)))
def cl_25438 : CNF.NClause := [(106,true),(41,false),(40,true),(34,true),(47,false),(53,false)]
theorem der_25438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25438 :=
  CNF.rup_sound cl_25438 [cl_2852,cl_25423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2852 v h) (hints_cons _ _ _ (der_25423 v h) (by intro d hd; cases hd)))
def cl_25439 : CNF.NClause := [(106,true),(47,false),(34,true),(41,true),(40,false),(53,false)]
theorem der_25439 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25439 :=
  CNF.rup_sound cl_25439 [cl_2854,cl_25424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2854 v h) (hints_cons _ _ _ (der_25424 v h) (by intro d hd; cases hd)))
def cl_25440 : CNF.NClause := [(106,true),(40,true),(41,true),(47,false),(53,false),(34,true)]
theorem der_25440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25440 :=
  CNF.rup_sound cl_25440 [cl_2856,cl_25425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2856 v h) (hints_cons _ _ _ (der_25425 v h) (by intro d hd; cases hd)))
def cl_25441 : CNF.NClause := [(106,true),(41,false),(34,true),(40,false),(47,true),(53,false)]
theorem der_25441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25441 :=
  CNF.rup_sound cl_25441 [cl_2858,cl_25426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2858 v h) (hints_cons _ _ _ (der_25426 v h) (by intro d hd; cases hd)))
def cl_25442 : CNF.NClause := [(106,true),(41,false),(40,true),(34,true),(47,true),(53,false)]
theorem der_25442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25442 :=
  CNF.rup_sound cl_25442 [cl_2860,cl_25427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2860 v h) (hints_cons _ _ _ (der_25427 v h) (by intro d hd; cases hd)))
def cl_25443 : CNF.NClause := [(106,true),(34,true),(41,true),(47,true),(40,false),(53,false)]
theorem der_25443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25443 :=
  CNF.rup_sound cl_25443 [cl_2862,cl_25428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2862 v h) (hints_cons _ _ _ (der_25428 v h) (by intro d hd; cases hd)))
def cl_25444 : CNF.NClause := [(106,true),(47,false),(41,false),(40,false),(53,true),(57,true)]
theorem der_25444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25444 :=
  CNF.rup_sound cl_25444 [cl_2866,cl_23738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2866 v h) (hints_cons _ _ _ (der_23738 v h) (by intro d hd; cases hd)))
def cl_25445 : CNF.NClause := [(106,true),(41,false),(40,true),(34,true),(47,false),(53,true)]
theorem der_25445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25445 :=
  CNF.rup_sound cl_25445 [cl_2868,cl_25431] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2868 v h) (hints_cons _ _ _ (der_25431 v h) (by intro d hd; cases hd)))
def cl_25446 : CNF.NClause := [(106,true),(47,false),(34,true),(41,true),(40,false),(53,true)]
theorem der_25446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25446 :=
  CNF.rup_sound cl_25446 [cl_2870,cl_25432] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2870 v h) (hints_cons _ _ _ (der_25432 v h) (by intro d hd; cases hd)))
def cl_25447 : CNF.NClause := [(106,true),(41,false),(40,false),(47,true),(53,true),(57,true)]
theorem der_25447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25447 :=
  CNF.rup_sound cl_25447 [cl_2874,cl_23751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2874 v h) (hints_cons _ _ _ (der_23751 v h) (by intro d hd; cases hd)))
def cl_25448 : CNF.NClause := [(111,true),(55,false),(38,false),(42,false),(46,false),(60,false)]
theorem der_25448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25448 :=
  CNF.rup_sound cl_25448 [cl_3138,cl_23717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3138 v h) (hints_cons _ _ _ (der_23717 v h) (by intro d hd; cases hd)))
def cl_25449 : CNF.NClause := [(111,true),(42,false),(38,true),(46,false),(55,false),(60,false)]
theorem der_25449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25449 :=
  CNF.rup_sound cl_25449 [cl_3140,cl_3139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3140 v h) (hints_cons _ _ _ (inp_3139 v h) (by intro d hd; cases hd)))
def cl_25450 : CNF.NClause := [(111,true),(55,false),(38,false),(42,true),(46,false),(60,false)]
theorem der_25450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25450 :=
  CNF.rup_sound cl_25450 [cl_3142,cl_25334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3142 v h) (hints_cons _ _ _ (der_25334 v h) (by intro d hd; cases hd)))
def cl_25451 : CNF.NClause := [(111,true),(60,false),(55,false),(42,true),(38,true),(46,false)]
theorem der_25451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25451 :=
  CNF.rup_sound cl_25451 [cl_3144,cl_25334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3144 v h) (hints_cons _ _ _ (der_25334 v h) (by intro d hd; cases hd)))
def cl_25452 : CNF.NClause := [(111,true),(55,false),(38,false),(42,false),(46,true),(60,false)]
theorem der_25452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25452 :=
  CNF.rup_sound cl_25452 [cl_3146,cl_25318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3146 v h) (hints_cons _ _ _ (der_25318 v h) (by intro d hd; cases hd)))
def cl_25453 : CNF.NClause := [(111,true),(42,false),(38,true),(46,true),(55,false),(60,false)]
theorem der_25453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25453 :=
  CNF.rup_sound cl_25453 [cl_3148,cl_23723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3148 v h) (hints_cons _ _ _ (der_23723 v h) (by intro d hd; cases hd)))
def cl_25454 : CNF.NClause := [(111,true),(55,false),(38,false),(42,true),(34,true),(60,false)]
theorem der_25454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25454 :=
  CNF.rup_sound cl_25454 [cl_3150,cl_25450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3150 v h) (hints_cons _ _ _ (der_25450 v h) (by intro d hd; cases hd)))
def cl_25455 : CNF.NClause := [(111,true),(60,false),(55,false),(42,true),(46,true),(34,true)]
theorem der_25455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25455 :=
  CNF.rup_sound cl_25455 [cl_3152,cl_25454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3152 v h) (hints_cons _ _ _ (der_25454 v h) (by intro d hd; cases hd)))
def cl_25456 : CNF.NClause := [(111,true),(38,false),(42,false),(46,false),(55,true),(60,false)]
theorem der_25456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25456 :=
  CNF.rup_sound cl_25456 [cl_3154,cl_25282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3154 v h) (hints_cons _ _ _ (der_25282 v h) (by intro d hd; cases hd)))
def cl_25457 : CNF.NClause := [(111,true),(46,false),(38,true),(60,false),(55,true),(42,false)]
theorem der_25457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25457 :=
  CNF.rup_sound cl_25457 [cl_3156,cl_25283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3156 v h) (hints_cons _ _ _ (der_25283 v h) (by intro d hd; cases hd)))
def cl_25458 : CNF.NClause := [(111,true),(38,false),(42,true),(46,false),(55,true),(60,false)]
theorem der_25458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25458 :=
  CNF.rup_sound cl_25458 [cl_3158,cl_25336] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3158 v h) (hints_cons _ _ _ (der_25336 v h) (by intro d hd; cases hd)))
def cl_25459 : CNF.NClause := [(111,true),(46,false),(38,true),(42,true),(60,false),(55,true)]
theorem der_25459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25459 :=
  CNF.rup_sound cl_25459 [cl_3160,cl_23727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3160 v h) (hints_cons _ _ _ (der_23727 v h) (by intro d hd; cases hd)))
def cl_25460 : CNF.NClause := [(111,true),(38,false),(42,false),(46,true),(55,true),(60,false)]
theorem der_25460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25460 :=
  CNF.rup_sound cl_25460 [cl_3162,cl_23721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3162 v h) (hints_cons _ _ _ (der_23721 v h) (by intro d hd; cases hd)))
def cl_25461 : CNF.NClause := [(111,true),(60,false),(38,true),(46,true),(55,true),(42,false)]
theorem der_25461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25461 :=
  CNF.rup_sound cl_25461 [cl_3164,cl_23720] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3164 v h) (hints_cons _ _ _ (der_23720 v h) (by intro d hd; cases hd)))
def cl_25462 : CNF.NClause := [(111,true),(38,false),(34,true),(42,true),(46,true),(60,false)]
theorem der_25462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25462 :=
  CNF.rup_sound cl_25462 [cl_3166,cl_25454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3166 v h) (hints_cons _ _ _ (der_25454 v h) (by intro d hd; cases hd)))
def cl_25463 : CNF.NClause := [(111,true),(55,false),(38,false),(42,false),(46,false),(60,true)]
theorem der_25463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25463 :=
  CNF.rup_sound cl_25463 [cl_3170,cl_25277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3170 v h) (hints_cons _ _ _ (der_25277 v h) (by intro d hd; cases hd)))
def cl_25464 : CNF.NClause := [(111,true),(42,false),(38,true),(46,false),(55,false),(60,true)]
theorem der_25464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25464 :=
  CNF.rup_sound cl_25464 [cl_3172,cl_25277] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3172 v h) (hints_cons _ _ _ (der_25277 v h) (by intro d hd; cases hd)))
def cl_25465 : CNF.NClause := [(111,true),(55,false),(38,false),(42,true),(46,false),(34,true)]
theorem der_25465 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25465 :=
  CNF.rup_sound cl_25465 [cl_3174,cl_25454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3174 v h) (hints_cons _ _ _ (der_25454 v h) (by intro d hd; cases hd)))
def cl_25466 : CNF.NClause := [(111,true),(55,false),(42,true),(46,false),(34,true),(60,true)]
theorem der_25466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25466 :=
  CNF.rup_sound cl_25466 [cl_3176,cl_25465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3176 v h) (hints_cons _ _ _ (der_25465 v h) (by intro d hd; cases hd)))
def cl_25467 : CNF.NClause := [(111,true),(55,false),(38,false),(42,false),(46,true),(60,true)]
theorem der_25467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25467 :=
  CNF.rup_sound cl_25467 [cl_3178,cl_25319] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3178 v h) (hints_cons _ _ _ (der_25319 v h) (by intro d hd; cases hd)))
def cl_25468 : CNF.NClause := [(111,true),(42,false),(38,true),(34,true),(46,true),(55,false)]
theorem der_25468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25468 :=
  CNF.rup_sound cl_25468 [cl_3180,cl_25453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3180 v h) (hints_cons _ _ _ (der_25453 v h) (by intro d hd; cases hd)))
def cl_25469 : CNF.NClause := [(111,true),(55,false),(38,false),(42,true),(46,true),(34,true)]
theorem der_25469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25469 :=
  CNF.rup_sound cl_25469 [cl_3182,cl_25454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3182 v h) (hints_cons _ _ _ (der_25454 v h) (by intro d hd; cases hd)))
def cl_25470 : CNF.NClause := [(111,true),(38,false),(42,false),(46,false),(55,true),(60,true)]
theorem der_25470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25470 :=
  CNF.rup_sound cl_25470 [cl_3186,cl_25284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3186 v h) (hints_cons _ _ _ (der_25284 v h) (by intro d hd; cases hd)))
def cl_25471 : CNF.NClause := [(111,true),(46,false),(38,true),(42,false),(55,true),(60,true)]
theorem der_25471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25471 :=
  CNF.rup_sound cl_25471 [cl_3188,cl_25285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3188 v h) (hints_cons _ _ _ (der_25285 v h) (by intro d hd; cases hd)))
def cl_25472 : CNF.NClause := [(111,true),(38,false),(34,true),(42,true),(46,false),(60,true)]
theorem der_25472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25472 :=
  CNF.rup_sound cl_25472 [cl_3190,cl_25465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3190 v h) (hints_cons _ _ _ (der_25465 v h) (by intro d hd; cases hd)))
def cl_25473 : CNF.NClause := [(111,true),(38,false),(42,false),(46,true),(55,true),(60,true)]
theorem der_25473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25473 :=
  CNF.rup_sound cl_25473 [cl_3194,cl_23721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3194 v h) (hints_cons _ _ _ (der_23721 v h) (by intro d hd; cases hd)))
def cl_25474 : CNF.NClause := [(116,true),(43,false),(36,true),(50,false),(52,false),(58,false)]
theorem der_25474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25474 :=
  CNF.rup_sound cl_25474 [cl_3460,cl_3459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3460 v h) (hints_cons _ _ _ (inp_3459 v h) (by intro d hd; cases hd)))
def cl_25475 : CNF.NClause := [(116,true),(50,false),(36,false),(34,true),(52,false),(58,false)]
theorem der_25475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25475 :=
  CNF.rup_sound cl_25475 [cl_3462,cl_3458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3462 v h) (hints_cons _ _ _ (inp_3458 v h) (by intro d hd; cases hd)))
def cl_25476 : CNF.NClause := [(116,true),(50,false),(36,true),(43,true),(52,false),(58,false)]
theorem der_25476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25476 :=
  CNF.rup_sound cl_25476 [cl_3464,cl_24911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3464 v h) (hints_cons _ _ _ (der_24911 v h) (by intro d hd; cases hd)))
def cl_25477 : CNF.NClause := [(116,true),(58,false),(36,false),(43,false),(52,false),(34,true)]
theorem der_25477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25477 :=
  CNF.rup_sound cl_25477 [cl_3466,cl_3458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3466 v h) (hints_cons _ _ _ (inp_3458 v h) (by intro d hd; cases hd)))
def cl_25478 : CNF.NClause := [(116,true),(58,false),(43,false),(50,true),(52,false),(36,true)]
theorem der_25478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25478 :=
  CNF.rup_sound cl_25478 [cl_3468,cl_24912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3468 v h) (hints_cons _ _ _ (der_24912 v h) (by intro d hd; cases hd)))
def cl_25479 : CNF.NClause := [(116,true),(58,false),(36,false),(43,true),(52,false),(34,true)]
theorem der_25479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25479 :=
  CNF.rup_sound cl_25479 [cl_3470,cl_25475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3470 v h) (hints_cons _ _ _ (der_25475 v h) (by intro d hd; cases hd)))
def cl_25480 : CNF.NClause := [(116,true),(58,false),(52,false),(43,true),(50,true),(36,true)]
theorem der_25480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25480 :=
  CNF.rup_sound cl_25480 [cl_3472,cl_24913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3472 v h) (hints_cons _ _ _ (der_24913 v h) (by intro d hd; cases hd)))
def cl_25481 : CNF.NClause := [(116,true),(50,false),(36,false),(43,false),(52,true),(58,false)]
theorem der_25481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25481 :=
  CNF.rup_sound cl_25481 [cl_3474,cl_3473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3474 v h) (hints_cons _ _ _ (inp_3473 v h) (by intro d hd; cases hd)))
def cl_25482 : CNF.NClause := [(116,true),(43,false),(36,true),(50,false),(52,true),(58,false)]
theorem der_25482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25482 :=
  CNF.rup_sound cl_25482 [cl_3476,cl_24914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3476 v h) (hints_cons _ _ _ (der_24914 v h) (by intro d hd; cases hd)))
def cl_25483 : CNF.NClause := [(116,true),(50,false),(36,false),(43,true),(34,true),(58,false)]
theorem der_25483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25483 :=
  CNF.rup_sound cl_25483 [cl_3478,cl_25475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3478 v h) (hints_cons _ _ _ (der_25475 v h) (by intro d hd; cases hd)))
def cl_25484 : CNF.NClause := [(116,true),(50,false),(36,true),(34,true),(43,true),(58,false)]
theorem der_25484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25484 :=
  CNF.rup_sound cl_25484 [cl_3480,cl_25476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3480 v h) (hints_cons _ _ _ (der_25476 v h) (by intro d hd; cases hd)))
def cl_25485 : CNF.NClause := [(116,true),(58,false),(36,false),(43,false),(52,true),(34,true)]
theorem der_25485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25485 :=
  CNF.rup_sound cl_25485 [cl_3482,cl_25481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3482 v h) (hints_cons _ _ _ (der_25481 v h) (by intro d hd; cases hd)))
def cl_25486 : CNF.NClause := [(116,true),(43,false),(34,true),(50,true),(58,false),(36,true)]
theorem der_25486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25486 :=
  CNF.rup_sound cl_25486 [cl_3484,cl_25478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3484 v h) (hints_cons _ _ _ (der_25478 v h) (by intro d hd; cases hd)))
def cl_25487 : CNF.NClause := [(116,true),(58,false),(36,false),(43,true),(50,true),(34,true)]
theorem der_25487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25487 :=
  CNF.rup_sound cl_25487 [cl_3486,cl_25479] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3486 v h) (hints_cons _ _ _ (der_25479 v h) (by intro d hd; cases hd)))
def cl_25488 : CNF.NClause := [(116,true),(50,false),(36,false),(43,false),(34,true),(52,false)]
theorem der_25488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25488 :=
  CNF.rup_sound cl_25488 [cl_3490,cl_3458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3490 v h) (hints_cons _ _ _ (inp_3458 v h) (by intro d hd; cases hd)))
def cl_25489 : CNF.NClause := [(116,true),(43,false),(36,true),(34,true),(50,false),(52,false)]
theorem der_25489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25489 :=
  CNF.rup_sound cl_25489 [cl_3492,cl_25474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3492 v h) (hints_cons _ _ _ (der_25474 v h) (by intro d hd; cases hd)))
def cl_25490 : CNF.NClause := [(116,true),(50,false),(36,false),(43,true),(34,true),(52,false)]
theorem der_25490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25490 :=
  CNF.rup_sound cl_25490 [cl_3494,cl_25475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3494 v h) (hints_cons _ _ _ (der_25475 v h) (by intro d hd; cases hd)))
def cl_25491 : CNF.NClause := [(116,true),(50,false),(36,true),(43,true),(52,false),(58,true)]
theorem der_25491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25491 :=
  CNF.rup_sound cl_25491 [cl_3496,cl_24919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3496 v h) (hints_cons _ _ _ (der_24919 v h) (by intro d hd; cases hd)))
def cl_25492 : CNF.NClause := [(116,true),(43,false),(36,false),(34,true),(52,false),(58,true)]
theorem der_25492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25492 :=
  CNF.rup_sound cl_25492 [cl_3498,cl_25488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3498 v h) (hints_cons _ _ _ (der_25488 v h) (by intro d hd; cases hd)))
def cl_25493 : CNF.NClause := [(116,true),(52,false),(43,false),(34,true),(50,true),(36,true)]
theorem der_25493 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25493 :=
  CNF.rup_sound cl_25493 [cl_3500,cl_25478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3500 v h) (hints_cons _ _ _ (der_25478 v h) (by intro d hd; cases hd)))
def cl_25494 : CNF.NClause := [(116,true),(52,false),(34,true),(50,true),(36,false),(58,true)]
theorem der_25494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25494 :=
  CNF.rup_sound cl_25494 [cl_3502,cl_25492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3502 v h) (hints_cons _ _ _ (der_25492 v h) (by intro d hd; cases hd)))
def cl_25495 : CNF.NClause := [(116,true),(50,false),(36,false),(43,false),(52,true),(58,true)]
theorem der_25495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25495 :=
  CNF.rup_sound cl_25495 [cl_3506,cl_23800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3506 v h) (hints_cons _ _ _ (der_23800 v h) (by intro d hd; cases hd)))
def cl_25496 : CNF.NClause := [(116,true),(43,false),(36,true),(50,false),(52,true),(58,true)]
theorem der_25496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25496 :=
  CNF.rup_sound cl_25496 [cl_3508,cl_24922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3508 v h) (hints_cons _ _ _ (der_24922 v h) (by intro d hd; cases hd)))
def cl_25497 : CNF.NClause := [(116,true),(50,false),(36,false),(43,true),(34,true),(58,true)]
theorem der_25497 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25497 :=
  CNF.rup_sound cl_25497 [cl_3510,cl_25490] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3510 v h) (hints_cons _ _ _ (der_25490 v h) (by intro d hd; cases hd)))
def cl_25498 : CNF.NClause := [(116,true),(36,false),(43,false),(50,true),(34,true),(58,true)]
theorem der_25498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25498 :=
  CNF.rup_sound cl_25498 [cl_3514,cl_25492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3514 v h) (hints_cons _ _ _ (der_25492 v h) (by intro d hd; cases hd)))
def cl_25499 : CNF.NClause := [(118,true),(61,false),(32,false),(33,false),(34,true),(35,false)]
theorem der_25499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25499 :=
  CNF.rup_sound cl_25499 [cl_3594,cl_25077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3594 v h) (hints_cons _ _ _ (der_25077 v h) (by intro d hd; cases hd)))
def cl_25500 : CNF.NClause := [(118,true),(61,false),(32,true),(33,false),(34,true),(35,false)]
theorem der_25500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25500 :=
  CNF.rup_sound cl_25500 [cl_3596,cl_25078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3596 v h) (hints_cons _ _ _ (der_25078 v h) (by intro d hd; cases hd)))
def cl_25501 : CNF.NClause := [(118,true),(61,false),(32,false),(31,true),(34,true),(35,false)]
theorem der_25501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25501 :=
  CNF.rup_sound cl_25501 [cl_3598,cl_25499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3598 v h) (hints_cons _ _ _ (der_25499 v h) (by intro d hd; cases hd)))
def cl_25502 : CNF.NClause := [(118,true),(61,false),(32,false),(33,false),(31,true),(34,true)]
theorem der_25502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25502 :=
  CNF.rup_sound cl_25502 [cl_3610,cl_25499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3610 v h) (hints_cons _ _ _ (der_25499 v h) (by intro d hd; cases hd)))
def cl_25504 : CNF.NClause := [(118,true),(61,false),(32,false),(33,true),(31,true),(34,true)]
theorem der_25504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25504 :=
  CNF.rup_sound cl_25504 [cl_3614,cl_25501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3614 v h) (hints_cons _ _ _ (der_25501 v h) (by intro d hd; cases hd)))
def cl_25505 : CNF.NClause := [(118,true),(32,false),(33,true),(35,false),(31,true),(34,true)]
theorem der_25505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25505 :=
  CNF.rup_sound cl_25505 [cl_3630,cl_25504] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3630 v h) (hints_cons _ _ _ (der_25504 v h) (by intro d hd; cases hd)))
def cl_25506 : CNF.NClause := [(118,true),(33,false),(32,false),(31,true),(35,false),(61,true)]
theorem der_25506 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25506 :=
  CNF.rup_sound cl_25506 [cl_3626,cl_3618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3626 v h) (hints_cons _ _ _ (inp_3618 v h) (by intro d hd; cases hd)))
def cl_25507 : CNF.NClause := [(118,true),(33,false),(32,true),(31,true),(34,true),(35,false)]
theorem der_25507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25507 :=
  CNF.rup_sound cl_25507 [cl_3628,cl_25500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3628 v h) (hints_cons _ _ _ (der_25500 v h) (by intro d hd; cases hd)))
def cl_25508 : CNF.NClause := [(118,true),(32,false),(31,true),(33,false),(34,true),(35,true)]
theorem der_25508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25508 :=
  CNF.rup_sound cl_25508 [cl_3642,cl_25502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3642 v h) (hints_cons _ _ _ (der_25502 v h) (by intro d hd; cases hd)))
def cl_25509 : CNF.NClause := [(109,true),(46,true),(35,false),(44,false),(37,false),(58,true)]
theorem der_25509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25509 :=
  CNF.rup_sound cl_25509 [cl_3049,cl_23768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3049 v h) (hints_cons _ _ _ (der_23768 v h) (by intro d hd; cases hd)))
def cl_25510 : CNF.NClause := [(56,false),(92,false),(62,false),(65,false),(63,false),(66,false)]
theorem der_25510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25510 :=
  CNF.rup_sound cl_25510 [cl_15493,cl_15489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15493 v h) (hints_cons _ _ _ (der_15489 v h) (by intro d hd; cases hd)))
def cl_25511 : CNF.NClause := [(56,false),(62,false),(63,false),(66,false),(92,false),(64,true)]
theorem der_25511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25511 :=
  CNF.rup_sound cl_25511 [cl_15501,cl_25510] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15501 v h) (hints_cons _ _ _ (der_25510 v h) (by intro d hd; cases hd)))
def cl_25512 : CNF.NClause := [(56,false),(66,true),(62,false),(65,false),(92,false),(64,true)]
theorem der_25512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25512 :=
  CNF.rup_sound cl_25512 [cl_15509,cl_25020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15509 v h) (hints_cons _ _ _ (der_25020 v h) (by intro d hd; cases hd)))
def cl_25513 : CNF.NClause := [(56,false),(66,true),(92,false),(63,false),(65,true),(62,false)]
theorem der_25513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25513 :=
  CNF.rup_sound cl_25513 [cl_15517,cl_24698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15517 v h) (hints_cons _ _ _ (der_24698 v h) (by intro d hd; cases hd)))
def cl_25514 : CNF.NClause := [(56,false),(92,true),(62,false),(65,false),(63,false),(66,false)]
theorem der_25514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25514 :=
  CNF.rup_sound cl_25514 [cl_15525,cl_25023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15525 v h) (hints_cons _ _ _ (der_25023 v h) (by intro d hd; cases hd)))
def cl_25515 : CNF.NClause := [(56,false),(62,false),(92,true),(66,false),(65,true),(63,false)]
theorem der_25515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25515 :=
  CNF.rup_sound cl_25515 [cl_15533,cl_24699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15533 v h) (hints_cons _ _ _ (der_24699 v h) (by intro d hd; cases hd)))
def cl_25516 : CNF.NClause := [(56,false),(66,true),(62,false),(65,false),(92,true),(64,true)]
theorem der_25516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25516 :=
  CNF.rup_sound cl_25516 [cl_15541,cl_25028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15541 v h) (hints_cons _ _ _ (der_25028 v h) (by intro d hd; cases hd)))
def cl_25517 : CNF.NClause := [(56,false),(62,false),(63,false),(65,true),(64,true),(92,true)]
theorem der_25517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25517 :=
  CNF.rup_sound cl_25517 [cl_15549,cl_25515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15549 v h) (hints_cons _ _ _ (der_25515 v h) (by intro d hd; cases hd)))
def cl_25518 : CNF.NClause := [(56,false),(63,true),(62,true),(66,false),(92,false),(64,true)]
theorem der_25518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25518 :=
  CNF.rup_sound cl_25518 [cl_15496,cl_24700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15496 v h) (hints_cons _ _ _ (der_24700 v h) (by intro d hd; cases hd)))
def cl_25519 : CNF.NClause := [(56,false),(66,true),(62,true),(63,true),(64,true),(92,false)]
theorem der_25519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25519 :=
  CNF.rup_sound cl_25519 [cl_15512,cl_24700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15512 v h) (hints_cons _ _ _ (der_24700 v h) (by intro d hd; cases hd)))
def cl_25520 : CNF.NClause := [(56,false),(92,true),(63,true),(65,false),(64,true),(66,false)]
theorem der_25520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25520 :=
  CNF.rup_sound cl_25520 [cl_15528,cl_25028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15528 v h) (hints_cons _ _ _ (der_25028 v h) (by intro d hd; cases hd)))
def cl_25521 : CNF.NClause := [(56,false),(66,true),(63,true),(65,false),(64,true),(92,true)]
theorem der_25521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25521 :=
  CNF.rup_sound cl_25521 [cl_15544,cl_25028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15544 v h) (hints_cons _ _ _ (der_25028 v h) (by intro d hd; cases hd)))
def cl_25522 : CNF.NClause := [(56,false),(62,true),(65,false),(66,false),(63,false),(92,false)]
theorem der_25522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25522 :=
  CNF.rup_sound cl_25522 [cl_15494,cl_23668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15494 v h) (hints_cons _ _ _ (der_23668 v h) (by intro d hd; cases hd)))
def cl_25523 : CNF.NClause := [(56,false),(65,true),(62,true),(64,true),(66,false),(92,false)]
theorem der_25523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25523 :=
  CNF.rup_sound cl_25523 [cl_15502,cl_24700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15502 v h) (hints_cons _ _ _ (der_24700 v h) (by intro d hd; cases hd)))
def cl_25524 : CNF.NClause := [(56,false),(63,false),(62,true),(64,true),(65,false),(92,false)]
theorem der_25524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25524 :=
  CNF.rup_sound cl_25524 [cl_15510,cl_25522] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15510 v h) (hints_cons _ _ _ (der_25522 v h) (by intro d hd; cases hd)))
def cl_25525 : CNF.NClause := [(56,false),(65,true),(62,true),(64,true),(66,true),(92,false)]
theorem der_25525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25525 :=
  CNF.rup_sound cl_25525 [cl_15518,cl_24700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15518 v h) (hints_cons _ _ _ (der_24700 v h) (by intro d hd; cases hd)))
def cl_25526 : CNF.NClause := [(56,false),(92,true),(63,false),(62,true),(65,false),(66,false)]
theorem der_25526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25526 :=
  CNF.rup_sound cl_25526 [cl_15526,cl_23669] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15526 v h) (hints_cons _ _ _ (der_23669 v h) (by intro d hd; cases hd)))
def cl_25527 : CNF.NClause := [(56,false),(65,true),(63,false),(62,true),(64,true),(66,false)]
theorem der_25527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25527 :=
  CNF.rup_sound cl_25527 [cl_15534,cl_25523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15534 v h) (hints_cons _ _ _ (der_25523 v h) (by intro d hd; cases hd)))
def cl_25528 : CNF.NClause := [(56,false),(66,true),(63,false),(62,true),(65,false),(92,true)]
theorem der_25528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25528 :=
  CNF.rup_sound cl_25528 [cl_15542,cl_24707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15542 v h) (hints_cons _ _ _ (der_24707 v h) (by intro d hd; cases hd)))
def cl_25529 : CNF.NClause := [(56,false),(65,true),(63,false),(62,true),(66,true),(92,true)]
theorem der_25529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25529 :=
  CNF.rup_sound cl_25529 [cl_15550,cl_24707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15550 v h) (hints_cons _ _ _ (der_24707 v h) (by intro d hd; cases hd)))
def cl_25530 : CNF.NClause := [(93,true),(57,false),(58,false),(59,false),(60,false),(61,false)]
theorem der_25530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25530 :=
  CNF.rup_sound cl_25530 [cl_1985,cl_25266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1985 v h) (hints_cons _ _ _ (der_25266 v h) (by intro d hd; cases hd)))
def cl_25531 : CNF.NClause := [(93,true),(56,false),(58,false),(59,false),(60,false),(61,false)]
theorem der_25531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25531 :=
  CNF.rup_sound cl_25531 [cl_1987,cl_25530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1987 v h) (hints_cons _ _ _ (der_25530 v h) (by intro d hd; cases hd)))
def cl_25532 : CNF.NClause := [(93,true),(57,false),(58,true),(59,false),(60,false),(61,false)]
theorem der_25532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25532 :=
  CNF.rup_sound cl_25532 [cl_1989,cl_1990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1989 v h) (hints_cons _ _ _ (inp_1990 v h) (by intro d hd; cases hd)))
def cl_25533 : CNF.NClause := [(93,true),(56,false),(57,true),(59,false),(60,false),(61,false)]
theorem der_25533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25533 :=
  CNF.rup_sound cl_25533 [cl_1991,cl_25531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1991 v h) (hints_cons _ _ _ (der_25531 v h) (by intro d hd; cases hd)))
def cl_25534 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(60,false),(61,false)]
theorem der_25534 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25534 :=
  CNF.rup_sound cl_25534 [cl_1993,cl_25530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1993 v h) (hints_cons _ _ _ (der_25530 v h) (by intro d hd; cases hd)))
def cl_25535 : CNF.NClause := [(93,true),(56,false),(57,true),(58,false),(60,false),(61,false)]
theorem der_25535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25535 :=
  CNF.rup_sound cl_25535 [cl_1995,cl_25531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1995 v h) (hints_cons _ _ _ (der_25531 v h) (by intro d hd; cases hd)))
def cl_25536 : CNF.NClause := [(93,true),(57,false),(58,true),(59,true),(60,false),(61,false)]
theorem der_25536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25536 :=
  CNF.rup_sound cl_25536 [cl_1997,cl_25039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1997 v h) (hints_cons _ _ _ (der_25039 v h) (by intro d hd; cases hd)))
def cl_25537 : CNF.NClause := [(93,true),(56,false),(57,true),(58,true),(60,false),(61,false)]
theorem der_25537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25537 :=
  CNF.rup_sound cl_25537 [cl_1999,cl_25533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1999 v h) (hints_cons _ _ _ (der_25533 v h) (by intro d hd; cases hd)))
def cl_25538 : CNF.NClause := [(93,true),(57,false),(58,false),(59,false),(60,true),(61,false)]
theorem der_25538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25538 :=
  CNF.rup_sound cl_25538 [cl_2001,cl_2002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2001 v h) (hints_cons _ _ _ (inp_2002 v h) (by intro d hd; cases hd)))
def cl_25540 : CNF.NClause := [(93,true),(57,false),(58,true),(59,false),(60,true),(61,false)]
theorem der_25540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25540 :=
  CNF.rup_sound cl_25540 [cl_2005,cl_25040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2005 v h) (hints_cons _ _ _ (der_25040 v h) (by intro d hd; cases hd)))
def cl_25542 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(60,true),(61,false)]
theorem der_25542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25542 :=
  CNF.rup_sound cl_25542 [cl_2009,cl_25538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2009 v h) (hints_cons _ _ _ (der_25538 v h) (by intro d hd; cases hd)))
def cl_25544 : CNF.NClause := [(93,true),(57,false),(58,true),(59,true),(60,true),(61,false)]
theorem der_25544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25544 :=
  CNF.rup_sound cl_25544 [cl_2013,cl_25041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2013 v h) (hints_cons _ _ _ (der_25041 v h) (by intro d hd; cases hd)))
def cl_25546 : CNF.NClause := [(93,true),(57,false),(58,false),(59,false),(60,false),(61,true)]
theorem der_25546 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25546 :=
  CNF.rup_sound cl_25546 [cl_2017,cl_23838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2017 v h) (hints_cons _ _ _ (der_23838 v h) (by intro d hd; cases hd)))
def cl_25547 : CNF.NClause := [(93,true),(56,false),(57,true),(58,false),(59,false),(60,false)]
theorem der_25547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25547 :=
  CNF.rup_sound cl_25547 [cl_2019,cl_25531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2019 v h) (hints_cons _ _ _ (der_25531 v h) (by intro d hd; cases hd)))
def cl_25548 : CNF.NClause := [(93,true),(56,false),(57,false),(58,true),(59,false),(60,false)]
theorem der_25548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25548 :=
  CNF.rup_sound cl_25548 [cl_2021,cl_25532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2021 v h) (hints_cons _ _ _ (der_25532 v h) (by intro d hd; cases hd)))
def cl_25549 : CNF.NClause := [(93,true),(56,false),(57,true),(58,true),(59,false),(60,false)]
theorem der_25549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25549 :=
  CNF.rup_sound cl_25549 [cl_2023,cl_25533] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2023 v h) (hints_cons _ _ _ (der_25533 v h) (by intro d hd; cases hd)))
def cl_25550 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(59,true),(60,false)]
theorem der_25550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25550 :=
  CNF.rup_sound cl_25550 [cl_2025,cl_25534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2025 v h) (hints_cons _ _ _ (der_25534 v h) (by intro d hd; cases hd)))
def cl_25551 : CNF.NClause := [(93,true),(56,false),(57,true),(58,false),(59,true),(60,false)]
theorem der_25551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25551 :=
  CNF.rup_sound cl_25551 [cl_2027,cl_25535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2027 v h) (hints_cons _ _ _ (der_25535 v h) (by intro d hd; cases hd)))
def cl_25552 : CNF.NClause := [(93,true),(57,false),(58,true),(59,true),(60,false),(61,true)]
theorem der_25552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25552 :=
  CNF.rup_sound cl_25552 [cl_2029,cl_25045] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2029 v h) (hints_cons _ _ _ (der_25045 v h) (by intro d hd; cases hd)))
def cl_25554 : CNF.NClause := [(93,true),(57,false),(58,false),(59,false),(60,true),(61,true)]
theorem der_25554 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25554 :=
  CNF.rup_sound cl_25554 [cl_2033,cl_23791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2033 v h) (hints_cons _ _ _ (der_23791 v h) (by intro d hd; cases hd)))
def cl_25556 : CNF.NClause := [(93,true),(57,false),(58,true),(59,false),(60,true),(61,true)]
theorem der_25556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25556 :=
  CNF.rup_sound cl_25556 [cl_2037,cl_25046] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2037 v h) (hints_cons _ _ _ (der_25046 v h) (by intro d hd; cases hd)))
def cl_25558 : CNF.NClause := [(93,true),(56,false),(57,false),(58,false),(60,true),(61,true)]
theorem der_25558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25558 :=
  CNF.rup_sound cl_25558 [cl_2041,cl_25554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2041 v h) (hints_cons _ _ _ (der_25554 v h) (by intro d hd; cases hd)))
def cl_25561 : CNF.NClause := [(123,true),(36,false),(41,false),(46,false),(51,false),(31,true)]
theorem der_25561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25561 :=
  CNF.rup_sound cl_25561 [cl_3906,cl_23818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3906 v h) (hints_cons _ _ _ (der_23818 v h) (by intro d hd; cases hd)))
def cl_25562 : CNF.NClause := [(123,true),(36,true),(41,false),(46,false),(51,false),(31,true)]
theorem der_25562 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25562 :=
  CNF.rup_sound cl_25562 [cl_3908,cl_24910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3908 v h) (hints_cons _ _ _ (der_24910 v h) (by intro d hd; cases hd)))
def cl_25563 : CNF.NClause := [(123,true),(36,true),(41,true),(46,false),(51,false),(31,true)]
theorem der_25563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25563 :=
  CNF.rup_sound cl_25563 [cl_3912,cl_3944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3912 v h) (hints_cons _ _ _ (inp_3944 v h) (by intro d hd; cases hd)))
def cl_25564 : CNF.NClause := [(123,true),(56,false),(36,true),(41,true),(46,true),(51,false)]
theorem der_25564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25564 :=
  CNF.rup_sound cl_25564 [cl_3920,cl_25232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3920 v h) (hints_cons _ _ _ (der_25232 v h) (by intro d hd; cases hd)))
def cl_25567 : CNF.NClause := [(96,true),(56,false),(39,false),(44,false),(54,true),(34,false)]
theorem der_25567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25567 :=
  CNF.rup_sound cl_25567 [cl_2193,cl_2201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2193 v h) (hints_cons _ _ _ (inp_2201 v h) (by intro d hd; cases hd)))
def cl_25569 : CNF.NClause := [(94,true),(56,false),(40,false),(45,false),(50,false),(35,false)]
theorem der_25569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25569 :=
  CNF.rup_sound cl_25569 [cl_2049,cl_25279] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2049 v h) (hints_cons _ _ _ (der_25279 v h) (by intro d hd; cases hd)))
def cl_25570 : CNF.NClause := [(94,true),(40,true),(45,false),(35,false),(55,false),(50,false)]
theorem der_25570 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25570 :=
  CNF.rup_sound cl_25570 [cl_2051,cl_23851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2051 v h) (hints_cons _ _ _ (der_23851 v h) (by intro d hd; cases hd)))
def cl_25571 : CNF.NClause := [(97,true),(56,false),(42,false),(47,false),(52,false),(32,false)]
theorem der_25571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25571 :=
  CNF.rup_sound cl_25571 [cl_2241,cl_2243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2241 v h) (hints_cons _ _ _ (inp_2243 v h) (by intro d hd; cases hd)))
def cl_25572 : CNF.NClause := [(123,true),(36,false),(41,false),(31,true),(51,false),(46,true)]
theorem der_25572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25572 :=
  CNF.rup_sound cl_25572 [cl_3914,cl_3946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3914 v h) (hints_cons _ _ _ (inp_3946 v h) (by intro d hd; cases hd)))
def cl_25574 : CNF.NClause := [(97,true),(56,false),(42,false),(32,false),(52,false),(47,true)]
theorem der_25574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25574 :=
  CNF.rup_sound cl_25574 [cl_2249,cl_24776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2249 v h) (hints_cons _ _ _ (der_24776 v h) (by intro d hd; cases hd)))
def cl_25576 : CNF.NClause := [(94,true),(56,false),(40,false),(35,false),(50,false),(45,true)]
theorem der_25576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25576 :=
  CNF.rup_sound cl_25576 [cl_2053,cl_2069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2053 v h) (hints_cons _ _ _ (inp_2069 v h) (by intro d hd; cases hd)))
def cl_25577 : CNF.NClause := [(94,true),(40,true),(35,false),(50,false),(55,false),(45,true)]
theorem der_25577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25577 :=
  CNF.rup_sound cl_25577 [cl_2055,cl_2087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2055 v h) (hints_cons _ _ _ (inp_2087 v h) (by intro d hd; cases hd)))
def cl_25578 : CNF.NClause := [(94,true),(56,false),(40,false),(35,false),(55,false),(45,true)]
theorem der_25578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25578 :=
  CNF.rup_sound cl_25578 [cl_2061,cl_25576] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2061 v h) (hints_cons _ _ _ (der_25576 v h) (by intro d hd; cases hd)))
def cl_25579 : CNF.NClause := [(94,true),(56,false),(40,true),(35,false),(55,false),(45,true)]
theorem der_25579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25579 :=
  CNF.rup_sound cl_25579 [cl_2063,cl_25577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2063 v h) (hints_cons _ _ _ (der_25577 v h) (by intro d hd; cases hd)))
def cl_25580 : CNF.NClause := [(96,true),(56,false),(39,false),(44,false),(34,false),(49,true)]
theorem der_25580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25580 :=
  CNF.rup_sound cl_25580 [cl_2185,cl_2201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2185 v h) (hints_cons _ _ _ (inp_2201 v h) (by intro d hd; cases hd)))
def cl_25582 : CNF.NClause := [(97,true),(37,false),(42,false),(47,false),(32,false),(52,true)]
theorem der_25582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25582 :=
  CNF.rup_sound cl_25582 [cl_2257,cl_2289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2257 v h) (hints_cons _ _ _ (inp_2289 v h) (by intro d hd; cases hd)))
def cl_25583 : CNF.NClause := [(94,true),(56,false),(40,false),(45,false),(35,false),(55,false)]
theorem der_25583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25583 :=
  CNF.rup_sound cl_25583 [cl_2057,cl_25569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2057 v h) (hints_cons _ _ _ (der_25569 v h) (by intro d hd; cases hd)))
def cl_25584 : CNF.NClause := [(94,true),(56,false),(40,true),(45,false),(35,false),(55,false)]
theorem der_25584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25584 :=
  CNF.rup_sound cl_25584 [cl_2059,cl_25570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2059 v h) (hints_cons _ _ _ (der_25570 v h) (by intro d hd; cases hd)))
def cl_25587 : CNF.NClause := [(107,true),(32,false),(48,true),(41,false),(39,false),(58,false)]
theorem der_25587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25587 :=
  CNF.rup_sound cl_25587 [cl_2905,cl_2889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2905 v h) (hints_cons _ _ _ (inp_2889 v h) (by intro d hd; cases hd)))
def cl_25588 : CNF.NClause := [(107,true),(32,false),(48,true),(41,false),(39,false),(55,false)]
theorem der_25588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25588 :=
  CNF.rup_sound cl_25588 [cl_2921,cl_2889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2921 v h) (hints_cons _ _ _ (inp_2889 v h) (by intro d hd; cases hd)))
def cl_25589 : CNF.NClause := [(107,true),(32,false),(41,false),(39,false),(55,true),(58,true)]
theorem der_25589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25589 :=
  CNF.rup_sound cl_25589 [cl_2937,cl_25287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2937 v h) (hints_cons _ _ _ (der_25287 v h) (by intro d hd; cases hd)))
def cl_25590 : CNF.NClause := [(114,true),(48,true),(35,false),(36,false),(42,false),(57,false)]
theorem der_25590 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25590 :=
  CNF.rup_sound cl_25590 [cl_3353,cl_3337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3353 v h) (hints_cons _ _ _ (inp_3337 v h) (by intro d hd; cases hd)))
def cl_25591 : CNF.NClause := [(114,true),(48,true),(35,false),(36,false),(54,true),(57,true)]
theorem der_25591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25591 :=
  CNF.rup_sound cl_25591 [cl_3385,cl_25349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3385 v h) (hints_cons _ _ _ (der_25349 v h) (by intro d hd; cases hd)))
def cl_25592 : CNF.NClause := [(101,true),(48,true),(37,false),(34,false),(51,false),(59,false)]
theorem der_25592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25592 :=
  CNF.rup_sound cl_25592 [cl_2505,cl_2509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2505 v h) (hints_cons _ _ _ (inp_2509 v h) (by intro d hd; cases hd)))
def cl_25594 : CNF.NClause := [(108,true),(48,true),(46,false),(49,true),(50,false),(61,false)]
theorem der_25594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25594 :=
  CNF.rup_sound cl_25594 [cl_2957,cl_23697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2957 v h) (hints_cons _ _ _ (der_23697 v h) (by intro d hd; cases hd)))
def cl_25596 : CNF.NClause := [(108,true),(48,true),(46,false),(49,true),(50,true),(61,false)]
theorem der_25596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25596 :=
  CNF.rup_sound cl_25596 [cl_2973,cl_23697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2973 v h) (hints_cons _ _ _ (der_23697 v h) (by intro d hd; cases hd)))
def cl_25597 : CNF.NClause := [(108,true),(48,true),(47,false),(46,false),(49,true),(61,true)]
theorem der_25597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25597 :=
  CNF.rup_sound cl_25597 [cl_3005,cl_23860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3005 v h) (hints_cons _ _ _ (der_23860 v h) (by intro d hd; cases hd)))
def cl_25598 : CNF.NClause := [(95,true),(56,false),(33,false),(48,false),(53,false),(43,true)]
theorem der_25598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25598 :=
  CNF.rup_sound cl_25598 [cl_2117,cl_23783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2117 v h) (hints_cons _ _ _ (der_23783 v h) (by intro d hd; cases hd)))
def cl_25599 : CNF.NClause := [(95,true),(56,false),(38,false),(33,false),(53,false),(43,true)]
theorem der_25599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25599 :=
  CNF.rup_sound cl_25599 [cl_2125,cl_25598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2125 v h) (hints_cons _ _ _ (der_25598 v h) (by intro d hd; cases hd)))
def cl_25600 : CNF.NClause := [(95,true),(56,false),(38,false),(33,false),(48,false),(43,true)]
theorem der_25600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25600 :=
  CNF.rup_sound cl_25600 [cl_2133,cl_25598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2133 v h) (hints_cons _ _ _ (der_25598 v h) (by intro d hd; cases hd)))
def cl_25601 : CNF.NClause := [(95,true),(56,false),(38,false),(33,false),(48,true),(43,true)]
theorem der_25601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25601 :=
  CNF.rup_sound cl_25601 [cl_2141,cl_25599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2141 v h) (hints_cons _ _ _ (der_25599 v h) (by intro d hd; cases hd)))
def cl_25602 : CNF.NClause := [(95,true),(38,false),(33,false),(48,false),(53,false),(56,true)]
theorem der_25602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25602 :=
  CNF.rup_sound cl_25602 [cl_2149,cl_14710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2149 v h) (hints_cons _ _ _ (der_14710 v h) (by intro d hd; cases hd)))
def cl_25603 : CNF.NClause := [(95,true),(38,false),(33,false),(48,true),(53,false),(56,true)]
theorem der_25603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25603 :=
  CNF.rup_sound cl_25603 [cl_2157,cl_23780] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2157 v h) (hints_cons _ _ _ (der_23780 v h) (by intro d hd; cases hd)))
def cl_25604 : CNF.NClause := [(95,true),(38,false),(43,true),(33,false),(48,false),(53,true)]
theorem der_25604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25604 :=
  CNF.rup_sound cl_25604 [cl_2165,cl_25600] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2165 v h) (hints_cons _ _ _ (der_25600 v h) (by intro d hd; cases hd)))
def cl_25605 : CNF.NClause := [(95,true),(38,false),(33,false),(48,true),(53,true),(56,true)]
theorem der_25605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25605 :=
  CNF.rup_sound cl_25605 [cl_2173,cl_23780] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2173 v h) (hints_cons _ _ _ (der_23780 v h) (by intro d hd; cases hd)))
def cl_25606 : CNF.NClause := [(112,true),(40,false),(32,false),(46,false),(54,false),(59,false)]
theorem der_25606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25606 :=
  CNF.rup_sound cl_25606 [cl_3205,cl_25055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3205 v h) (hints_cons _ _ _ (der_25055 v h) (by intro d hd; cases hd)))
def cl_25607 : CNF.NClause := [(112,true),(40,false),(32,false),(46,true),(54,false),(59,false)]
theorem der_25607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25607 :=
  CNF.rup_sound cl_25607 [cl_3213,cl_25313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3213 v h) (hints_cons _ _ _ (der_25313 v h) (by intro d hd; cases hd)))
def cl_25608 : CNF.NClause := [(112,true),(40,false),(32,false),(46,false),(54,true),(59,false)]
theorem der_25608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25608 :=
  CNF.rup_sound cl_25608 [cl_3221,cl_25055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3221 v h) (hints_cons _ _ _ (der_25055 v h) (by intro d hd; cases hd)))
def cl_25609 : CNF.NClause := [(112,true),(40,false),(32,false),(46,true),(54,true),(59,false)]
theorem der_25609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25609 :=
  CNF.rup_sound cl_25609 [cl_3229,cl_25314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3229 v h) (hints_cons _ _ _ (der_25314 v h) (by intro d hd; cases hd)))
def cl_25610 : CNF.NClause := [(112,true),(43,true),(40,false),(32,false),(46,false),(54,false)]
theorem der_25610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25610 :=
  CNF.rup_sound cl_25610 [cl_3237,cl_25606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3237 v h) (hints_cons _ _ _ (der_25606 v h) (by intro d hd; cases hd)))
def cl_25611 : CNF.NClause := [(112,true),(43,true),(40,false),(32,false),(46,true),(54,false)]
theorem der_25611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25611 :=
  CNF.rup_sound cl_25611 [cl_3245,cl_25607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3245 v h) (hints_cons _ _ _ (der_25607 v h) (by intro d hd; cases hd)))
def cl_25612 : CNF.NClause := [(112,true),(40,false),(32,false),(46,false),(54,true),(59,true)]
theorem der_25612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25612 :=
  CNF.rup_sound cl_25612 [cl_3253,cl_25056] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3253 v h) (hints_cons _ _ _ (der_25056 v h) (by intro d hd; cases hd)))
def cl_25613 : CNF.NClause := [(112,true),(40,false),(32,false),(46,true),(54,true),(59,true)]
theorem der_25613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25613 :=
  CNF.rup_sound cl_25613 [cl_3261,cl_25315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3261 v h) (hints_cons _ _ _ (der_25315 v h) (by intro d hd; cases hd)))
def cl_25614 : CNF.NClause := [(116,true),(58,false),(34,false),(50,true),(52,false),(43,true)]
theorem der_25614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25614 :=
  CNF.rup_sound cl_25614 [cl_3469,cl_24913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3469 v h) (hints_cons _ _ _ (der_24913 v h) (by intro d hd; cases hd)))
def cl_25615 : CNF.NClause := [(116,true),(34,false),(43,true),(50,true),(52,false),(58,true)]
theorem der_25615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25615 :=
  CNF.rup_sound cl_25615 [cl_3501,cl_24921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3501 v h) (hints_cons _ _ _ (der_24921 v h) (by intro d hd; cases hd)))
def cl_25616 : CNF.NClause := [(116,true),(50,false),(36,false),(34,false),(52,true),(58,true)]
theorem der_25616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25616 :=
  CNF.rup_sound cl_25616 [cl_3509,cl_23800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3509 v h) (hints_cons _ _ _ (der_23800 v h) (by intro d hd; cases hd)))
def cl_25617 : CNF.NClause := [(116,true),(34,false),(36,false),(43,true),(50,true),(58,true)]
theorem der_25617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25617 :=
  CNF.rup_sound cl_25617 [cl_3517,cl_25615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3517 v h) (hints_cons _ _ _ (der_25615 v h) (by intro d hd; cases hd)))
def cl_25618 : CNF.NClause := [(103,true),(41,false),(43,true),(42,false),(44,false),(45,false)]
theorem der_25618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25618 :=
  CNF.rup_sound cl_25618 [cl_2661,cl_25269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2661 v h) (hints_cons _ _ _ (der_25269 v h) (by intro d hd; cases hd)))
def cl_25619 : CNF.NClause := [(103,true),(41,false),(43,true),(42,false),(44,true),(45,false)]
theorem der_25619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25619 :=
  CNF.rup_sound cl_25619 [cl_2669,cl_23877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2669 v h) (hints_cons _ _ _ (der_23877 v h) (by intro d hd; cases hd)))
def cl_25620 : CNF.NClause := [(103,true),(41,false),(43,true),(42,false),(44,false),(45,true)]
theorem der_25620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25620 :=
  CNF.rup_sound cl_25620 [cl_2677,cl_25272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2677 v h) (hints_cons _ _ _ (der_25272 v h) (by intro d hd; cases hd)))
def cl_25621 : CNF.NClause := [(103,true),(41,false),(42,false),(44,true),(45,true),(61,true)]
theorem der_25621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25621 :=
  CNF.rup_sound cl_25621 [cl_2685,cl_2681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2685 v h) (hints_cons _ _ _ (inp_2681 v h) (by intro d hd; cases hd)))
def cl_25622 : CNF.NClause := [(99,true),(51,false),(35,false),(39,false),(47,false),(60,false)]
theorem der_25622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25622 :=
  CNF.rup_sound cl_25622 [cl_2373,cl_2369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2373 v h) (hints_cons _ _ _ (inp_2369 v h) (by intro d hd; cases hd)))
def cl_25623 : CNF.NClause := [(99,true),(51,false),(35,false),(39,false),(47,true),(60,false)]
theorem der_25623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25623 :=
  CNF.rup_sound cl_25623 [cl_2381,cl_23841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2381 v h) (hints_cons _ _ _ (der_23841 v h) (by intro d hd; cases hd)))
def cl_25624 : CNF.NClause := [(99,true),(35,false),(43,true),(39,false),(47,false),(60,false)]
theorem der_25624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25624 :=
  CNF.rup_sound cl_25624 [cl_2389,cl_25622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2389 v h) (hints_cons _ _ _ (der_25622 v h) (by intro d hd; cases hd)))
def cl_25625 : CNF.NClause := [(99,true),(35,false),(43,true),(39,false),(47,true),(60,false)]
theorem der_25625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25625 :=
  CNF.rup_sound cl_25625 [cl_2397,cl_25623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2397 v h) (hints_cons _ _ _ (der_25623 v h) (by intro d hd; cases hd)))
def cl_25626 : CNF.NClause := [(99,true),(51,false),(35,false),(39,false),(47,false),(43,true)]
theorem der_25626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25626 :=
  CNF.rup_sound cl_25626 [cl_2405,cl_25622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2405 v h) (hints_cons _ _ _ (der_25622 v h) (by intro d hd; cases hd)))
def cl_25627 : CNF.NClause := [(99,true),(51,false),(35,false),(39,false),(47,true),(60,true)]
theorem der_25627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25627 :=
  CNF.rup_sound cl_25627 [cl_2413,cl_2409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2413 v h) (hints_cons _ _ _ (inp_2409 v h) (by intro d hd; cases hd)))
def cl_25628 : CNF.NClause := [(99,true),(35,false),(43,true),(39,false),(47,false),(51,true)]
theorem der_25628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25628 :=
  CNF.rup_sound cl_25628 [cl_2421,cl_25624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2421 v h) (hints_cons _ _ _ (der_25624 v h) (by intro d hd; cases hd)))
def cl_25629 : CNF.NClause := [(99,true),(35,false),(43,true),(39,false),(47,true),(51,true)]
theorem der_25629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25629 :=
  CNF.rup_sound cl_25629 [cl_2429,cl_25625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2429 v h) (hints_cons _ _ _ (der_25625 v h) (by intro d hd; cases hd)))
def cl_25630 : CNF.NClause := [(122,true),(55,false),(31,true),(49,false),(43,true),(57,false)]
theorem der_25630 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25630 :=
  CNF.rup_sound cl_25630 [cl_3846,cl_3848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3846 v h) (hints_cons _ _ _ (inp_3848 v h) (by intro d hd; cases hd)))
def cl_25631 : CNF.NClause := [(122,true),(57,false),(37,false),(31,true),(55,true),(43,true)]
theorem der_25631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25631 :=
  CNF.rup_sound cl_25631 [cl_3862,cl_23810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3862 v h) (hints_cons _ _ _ (der_23810 v h) (by intro d hd; cases hd)))
def cl_25632 : CNF.NClause := [(122,true),(37,false),(43,true),(31,true),(49,false),(55,true)]
theorem der_25632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25632 :=
  CNF.rup_sound cl_25632 [cl_3894,cl_25631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3894 v h) (hints_cons _ _ _ (der_25631 v h) (by intro d hd; cases hd)))
def cl_25633 : CNF.NClause := [(116,true),(50,false),(43,true),(34,false),(52,false),(58,false)]
theorem der_25633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25633 :=
  CNF.rup_sound cl_25633 [cl_3461,cl_24911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3461 v h) (hints_cons _ _ _ (der_24911 v h) (by intro d hd; cases hd)))
def cl_25634 : CNF.NClause := [(112,true),(40,true),(32,false),(46,false),(54,false),(59,false)]
theorem der_25634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25634 :=
  CNF.rup_sound cl_25634 [cl_3207,cl_23790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3207 v h) (hints_cons _ _ _ (der_23790 v h) (by intro d hd; cases hd)))
def cl_25635 : CNF.NClause := [(112,true),(40,true),(32,false),(46,true),(54,false),(59,false)]
theorem der_25635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25635 :=
  CNF.rup_sound cl_25635 [cl_3215,cl_3211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3215 v h) (hints_cons _ _ _ (inp_3211 v h) (by intro d hd; cases hd)))
def cl_25636 : CNF.NClause := [(112,true),(40,true),(32,false),(46,false),(54,true),(59,false)]
theorem der_25636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25636 :=
  CNF.rup_sound cl_25636 [cl_3223,cl_25061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3223 v h) (hints_cons _ _ _ (der_25061 v h) (by intro d hd; cases hd)))
def cl_25637 : CNF.NClause := [(112,true),(40,true),(32,false),(46,true),(54,true),(59,false)]
theorem der_25637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25637 :=
  CNF.rup_sound cl_25637 [cl_3231,cl_23899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3231 v h) (hints_cons _ _ _ (der_23899 v h) (by intro d hd; cases hd)))
def cl_25638 : CNF.NClause := [(112,true),(43,true),(32,false),(46,false),(54,false),(59,true)]
theorem der_25638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25638 :=
  CNF.rup_sound cl_25638 [cl_3239,cl_25610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3239 v h) (hints_cons _ _ _ (der_25610 v h) (by intro d hd; cases hd)))
def cl_25639 : CNF.NClause := [(112,true),(43,true),(40,true),(32,false),(54,false),(59,true)]
theorem der_25639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25639 :=
  CNF.rup_sound cl_25639 [cl_3247,cl_25638] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3247 v h) (hints_cons _ _ _ (der_25638 v h) (by intro d hd; cases hd)))
def cl_25640 : CNF.NClause := [(112,true),(40,true),(32,false),(46,false),(54,true),(59,true)]
theorem der_25640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25640 :=
  CNF.rup_sound cl_25640 [cl_3255,cl_25062] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3255 v h) (hints_cons _ _ _ (der_25062 v h) (by intro d hd; cases hd)))
def cl_25641 : CNF.NClause := [(122,true),(37,false),(49,true),(31,true),(43,true),(57,false)]
theorem der_25641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25641 :=
  CNF.rup_sound cl_25641 [cl_3854,cl_23810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3854 v h) (hints_cons _ _ _ (der_23810 v h) (by intro d hd; cases hd)))
def cl_25642 : CNF.NClause := [(116,true),(34,false),(36,false),(52,true),(50,true),(43,true)]
theorem der_25642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25642 :=
  CNF.rup_sound cl_25642 [cl_3485,cl_25617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3485 v h) (hints_cons _ _ _ (der_25617 v h) (by intro d hd; cases hd)))
def cl_25643 : CNF.NClause := [(116,true),(50,false),(36,false),(52,true),(34,false),(58,false)]
theorem der_25643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25643 :=
  CNF.rup_sound cl_25643 [cl_3477,cl_3473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3477 v h) (hints_cons _ _ _ (inp_3473 v h) (by intro d hd; cases hd)))
def cl_25644 : CNF.NClause := [(95,true),(33,false),(38,true),(48,false),(53,false),(56,true)]
theorem der_25644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25644 :=
  CNF.rup_sound cl_25644 [cl_2151,cl_14710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2151 v h) (hints_cons _ _ _ (der_14710 v h) (by intro d hd; cases hd)))
def cl_25645 : CNF.NClause := [(95,true),(33,false),(43,true),(48,true),(53,false),(56,true)]
theorem der_25645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25645 :=
  CNF.rup_sound cl_25645 [cl_2159,cl_25603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2159 v h) (hints_cons _ _ _ (der_25603 v h) (by intro d hd; cases hd)))
def cl_25646 : CNF.NClause := [(95,true),(33,false),(38,true),(48,false),(53,true),(56,true)]
theorem der_25646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25646 :=
  CNF.rup_sound cl_25646 [cl_2167,cl_23769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2167 v h) (hints_cons _ _ _ (der_23769 v h) (by intro d hd; cases hd)))
def cl_25647 : CNF.NClause := [(95,true),(56,false),(38,false),(43,false),(48,false),(53,false)]
theorem der_25647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25647 :=
  CNF.rup_sound cl_25647 [cl_2114,cl_23777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2114 v h) (hints_cons _ _ _ (der_23777 v h) (by intro d hd; cases hd)))
def cl_25648 : CNF.NClause := [(95,true),(56,false),(38,true),(48,false),(53,false),(43,false)]
theorem der_25648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25648 :=
  CNF.rup_sound cl_25648 [cl_2116,cl_23783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2116 v h) (hints_cons _ _ _ (der_23783 v h) (by intro d hd; cases hd)))
def cl_25649 : CNF.NClause := [(95,true),(56,false),(38,false),(43,true),(48,false),(53,false)]
theorem der_25649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25649 :=
  CNF.rup_sound cl_25649 [cl_2118,cl_25598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2118 v h) (hints_cons _ _ _ (der_25598 v h) (by intro d hd; cases hd)))
def cl_25651 : CNF.NClause := [(95,true),(56,false),(38,false),(43,false),(48,true),(53,false)]
theorem der_25651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25651 :=
  CNF.rup_sound cl_25651 [cl_2122,cl_23778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2122 v h) (hints_cons _ _ _ (der_23778 v h) (by intro d hd; cases hd)))
def cl_25652 : CNF.NClause := [(95,true),(56,false),(38,true),(33,true),(53,false),(43,false)]
theorem der_25652 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25652 :=
  CNF.rup_sound cl_25652 [cl_2124,cl_25648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2124 v h) (hints_cons _ _ _ (der_25648 v h) (by intro d hd; cases hd)))
def cl_25653 : CNF.NClause := [(95,true),(56,false),(38,false),(43,true),(48,true),(53,false)]
theorem der_25653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25653 :=
  CNF.rup_sound cl_25653 [cl_2126,cl_25599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2126 v h) (hints_cons _ _ _ (der_25599 v h) (by intro d hd; cases hd)))
def cl_25655 : CNF.NClause := [(95,true),(56,false),(38,false),(43,false),(48,false),(53,true)]
theorem der_25655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25655 :=
  CNF.rup_sound cl_25655 [cl_2130,cl_23777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2130 v h) (hints_cons _ _ _ (der_23777 v h) (by intro d hd; cases hd)))
def cl_25656 : CNF.NClause := [(95,true),(56,false),(38,true),(33,true),(48,false),(43,false)]
theorem der_25656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25656 :=
  CNF.rup_sound cl_25656 [cl_2132,cl_25648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2132 v h) (hints_cons _ _ _ (der_25648 v h) (by intro d hd; cases hd)))
def cl_25657 : CNF.NClause := [(95,true),(56,false),(38,false),(43,true),(48,false),(53,true)]
theorem der_25657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25657 :=
  CNF.rup_sound cl_25657 [cl_2134,cl_25600] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2134 v h) (hints_cons _ _ _ (der_25600 v h) (by intro d hd; cases hd)))
def cl_25660 : CNF.NClause := [(95,true),(56,false),(38,true),(33,true),(53,true),(43,false)]
theorem der_25660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25660 :=
  CNF.rup_sound cl_25660 [cl_2140,cl_25656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2140 v h) (hints_cons _ _ _ (der_25656 v h) (by intro d hd; cases hd)))
def cl_25662 : CNF.NClause := [(95,true),(38,false),(43,false),(48,false),(53,false),(56,true)]
theorem der_25662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25662 :=
  CNF.rup_sound cl_25662 [cl_2146,cl_14710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2146 v h) (hints_cons _ _ _ (der_14710 v h) (by intro d hd; cases hd)))
def cl_25663 : CNF.NClause := [(95,true),(43,false),(38,true),(53,false),(48,false),(56,true)]
theorem der_25663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25663 :=
  CNF.rup_sound cl_25663 [cl_2148,cl_14710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2148 v h) (hints_cons _ _ _ (der_14710 v h) (by intro d hd; cases hd)))
def cl_25664 : CNF.NClause := [(95,true),(38,false),(43,true),(48,false),(53,false),(56,true)]
theorem der_25664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25664 :=
  CNF.rup_sound cl_25664 [cl_2150,cl_25602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2150 v h) (hints_cons _ _ _ (der_25602 v h) (by intro d hd; cases hd)))
def cl_25665 : CNF.NClause := [(95,true),(53,false),(38,true),(48,false),(43,true),(56,true)]
theorem der_25665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25665 :=
  CNF.rup_sound cl_25665 [cl_2152,cl_25644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2152 v h) (hints_cons _ _ _ (der_25644 v h) (by intro d hd; cases hd)))
def cl_25666 : CNF.NClause := [(95,true),(38,false),(43,false),(48,true),(53,false),(56,true)]
theorem der_25666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25666 :=
  CNF.rup_sound cl_25666 [cl_2154,cl_23780] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2154 v h) (hints_cons _ _ _ (der_23780 v h) (by intro d hd; cases hd)))
def cl_25667 : CNF.NClause := [(95,true),(43,false),(33,true),(48,true),(53,false),(56,true)]
theorem der_25667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25667 :=
  CNF.rup_sound cl_25667 [cl_2156,cl_25666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2156 v h) (hints_cons _ _ _ (der_25666 v h) (by intro d hd; cases hd)))
def cl_25668 : CNF.NClause := [(95,true),(38,false),(43,true),(48,true),(53,false),(56,true)]
theorem der_25668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25668 :=
  CNF.rup_sound cl_25668 [cl_2158,cl_25603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2158 v h) (hints_cons _ _ _ (der_25603 v h) (by intro d hd; cases hd)))
def cl_25669 : CNF.NClause := [(95,true),(38,false),(33,true),(43,false),(48,false),(53,true)]
theorem der_25669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25669 :=
  CNF.rup_sound cl_25669 [cl_2162,cl_25655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2162 v h) (hints_cons _ _ _ (der_25655 v h) (by intro d hd; cases hd)))
def cl_25670 : CNF.NClause := [(95,true),(48,false),(38,true),(43,false),(53,true),(56,true)]
theorem der_25670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25670 :=
  CNF.rup_sound cl_25670 [cl_2164,cl_23769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2164 v h) (hints_cons _ _ _ (der_23769 v h) (by intro d hd; cases hd)))
def cl_25671 : CNF.NClause := [(95,true),(38,false),(43,true),(48,false),(53,true),(56,true)]
theorem der_25671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25671 :=
  CNF.rup_sound cl_25671 [cl_2166,cl_25604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2166 v h) (hints_cons _ _ _ (der_25604 v h) (by intro d hd; cases hd)))
def cl_25672 : CNF.NClause := [(95,true),(38,false),(43,false),(48,true),(53,true),(56,true)]
theorem der_25672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25672 :=
  CNF.rup_sound cl_25672 [cl_2170,cl_23780] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2170 v h) (hints_cons _ _ _ (der_23780 v h) (by intro d hd; cases hd)))
def cl_25673 : CNF.NClause := [(100,true),(51,false),(33,true),(49,false),(42,false),(58,false)]
theorem der_25673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25673 :=
  CNF.rup_sound cl_25673 [cl_2436,cl_2434] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2436 v h) (hints_cons _ _ _ (inp_2434 v h) (by intro d hd; cases hd)))
def cl_25674 : CNF.NClause := [(100,true),(51,false),(42,true),(49,false),(40,false),(58,false)]
theorem der_25674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25674 :=
  CNF.rup_sound cl_25674 [cl_2438,cl_2437] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2438 v h) (hints_cons _ _ _ (inp_2437 v h) (by intro d hd; cases hd)))
def cl_25675 : CNF.NClause := [(100,true),(51,false),(40,true),(33,true),(58,false),(49,false)]
theorem der_25675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25675 :=
  CNF.rup_sound cl_25675 [cl_2440,cl_25673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2440 v h) (hints_cons _ _ _ (der_25673 v h) (by intro d hd; cases hd)))
def cl_25676 : CNF.NClause := [(100,true),(51,false),(42,false),(49,true),(40,false),(58,false)]
theorem der_25676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25676 :=
  CNF.rup_sound cl_25676 [cl_2442,cl_2441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2442 v h) (hints_cons _ _ _ (inp_2441 v h) (by intro d hd; cases hd)))
def cl_25677 : CNF.NClause := [(100,true),(51,false),(40,true),(49,true),(42,false),(58,false)]
theorem der_25677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25677 :=
  CNF.rup_sound cl_25677 [cl_2444,cl_23814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2444 v h) (hints_cons _ _ _ (der_23814 v h) (by intro d hd; cases hd)))
def cl_25678 : CNF.NClause := [(100,true),(51,false),(42,true),(49,true),(40,false),(58,false)]
theorem der_25678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25678 :=
  CNF.rup_sound cl_25678 [cl_2446,cl_25320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2446 v h) (hints_cons _ _ _ (der_25320 v h) (by intro d hd; cases hd)))
def cl_25679 : CNF.NClause := [(100,true),(40,true),(42,true),(33,true),(51,false),(58,false)]
theorem der_25679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25679 :=
  CNF.rup_sound cl_25679 [cl_2448,cl_25675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2448 v h) (hints_cons _ _ _ (der_25675 v h) (by intro d hd; cases hd)))
def cl_25680 : CNF.NClause := [(100,true),(58,false),(33,true),(42,false),(40,false),(49,false)]
theorem der_25680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25680 :=
  CNF.rup_sound cl_25680 [cl_2450,cl_2434] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2450 v h) (hints_cons _ _ _ (inp_2434 v h) (by intro d hd; cases hd)))
def cl_25681 : CNF.NClause := [(100,true),(58,false),(40,true),(33,true),(49,false),(42,false)]
theorem der_25681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25681 :=
  CNF.rup_sound cl_25681 [cl_2452,cl_25673] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2452 v h) (hints_cons _ _ _ (der_25673 v h) (by intro d hd; cases hd)))
def cl_25682 : CNF.NClause := [(100,true),(42,true),(40,false),(49,false),(51,true),(58,false)]
theorem der_25682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25682 :=
  CNF.rup_sound cl_25682 [cl_2454,cl_25321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2454 v h) (hints_cons _ _ _ (der_25321 v h) (by intro d hd; cases hd)))
def cl_25683 : CNF.NClause := [(100,true),(58,false),(40,true),(42,true),(51,true),(49,false)]
theorem der_25683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25683 :=
  CNF.rup_sound cl_25683 [cl_2456,cl_25360] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2456 v h) (hints_cons _ _ _ (der_25360 v h) (by intro d hd; cases hd)))
def cl_25684 : CNF.NClause := [(100,true),(40,false),(33,true),(42,false),(49,true),(58,false)]
theorem der_25684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25684 :=
  CNF.rup_sound cl_25684 [cl_2458,cl_25676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2458 v h) (hints_cons _ _ _ (der_25676 v h) (by intro d hd; cases hd)))
def cl_25685 : CNF.NClause := [(100,true),(40,true),(33,true),(42,false),(51,true),(58,false)]
theorem der_25685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25685 :=
  CNF.rup_sound cl_25685 [cl_2460,cl_25681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2460 v h) (hints_cons _ _ _ (der_25681 v h) (by intro d hd; cases hd)))
def cl_25686 : CNF.NClause := [(100,true),(42,true),(58,false),(49,true),(51,true),(40,false)]
theorem der_25686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25686 :=
  CNF.rup_sound cl_25686 [cl_2462,cl_25322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2462 v h) (hints_cons _ _ _ (der_25322 v h) (by intro d hd; cases hd)))
def cl_25687 : CNF.NClause := [(100,true),(51,false),(42,false),(49,false),(40,false),(58,true)]
theorem der_25687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25687 :=
  CNF.rup_sound cl_25687 [cl_2466,cl_25042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2466 v h) (hints_cons _ _ _ (der_25042 v h) (by intro d hd; cases hd)))
def cl_25688 : CNF.NClause := [(100,true),(51,false),(40,true),(49,false),(42,false),(58,true)]
theorem der_25688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25688 :=
  CNF.rup_sound cl_25688 [cl_2468,cl_25043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2468 v h) (hints_cons _ _ _ (der_25043 v h) (by intro d hd; cases hd)))
def cl_25689 : CNF.NClause := [(100,true),(51,false),(42,true),(49,false),(40,false),(58,true)]
theorem der_25689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25689 :=
  CNF.rup_sound cl_25689 [cl_2470,cl_25323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2470 v h) (hints_cons _ _ _ (der_25323 v h) (by intro d hd; cases hd)))
def cl_25690 : CNF.NClause := [(100,true),(58,true),(40,true),(33,true),(51,false),(49,false)]
theorem der_25690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25690 :=
  CNF.rup_sound cl_25690 [cl_2472,cl_25688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2472 v h) (hints_cons _ _ _ (der_25688 v h) (by intro d hd; cases hd)))
def cl_25691 : CNF.NClause := [(100,true),(51,false),(42,false),(49,true),(40,false),(58,true)]
theorem der_25691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25691 :=
  CNF.rup_sound cl_25691 [cl_2474,cl_23808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2474 v h) (hints_cons _ _ _ (der_23808 v h) (by intro d hd; cases hd)))
def cl_25692 : CNF.NClause := [(100,true),(51,false),(40,true),(33,true),(49,true),(42,false)]
theorem der_25692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25692 :=
  CNF.rup_sound cl_25692 [cl_2476,cl_25677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2476 v h) (hints_cons _ _ _ (der_25677 v h) (by intro d hd; cases hd)))
def cl_25693 : CNF.NClause := [(100,true),(51,false),(42,true),(49,true),(40,false),(58,true)]
theorem der_25693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25693 :=
  CNF.rup_sound cl_25693 [cl_2478,cl_25324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2478 v h) (hints_cons _ _ _ (der_25324 v h) (by intro d hd; cases hd)))
def cl_25694 : CNF.NClause := [(100,true),(40,false),(33,true),(42,false),(49,false),(51,true)]
theorem der_25694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25694 :=
  CNF.rup_sound cl_25694 [cl_2482,cl_25680] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2482 v h) (hints_cons _ _ _ (der_25680 v h) (by intro d hd; cases hd)))
def cl_25695 : CNF.NClause := [(100,true),(49,false),(40,true),(42,false),(33,true),(51,true)]
theorem der_25695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25695 :=
  CNF.rup_sound cl_25695 [cl_2484,cl_25685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2484 v h) (hints_cons _ _ _ (der_25685 v h) (by intro d hd; cases hd)))
def cl_25696 : CNF.NClause := [(100,true),(42,true),(33,true),(40,false),(49,false),(58,true)]
theorem der_25696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25696 :=
  CNF.rup_sound cl_25696 [cl_2486,cl_25689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2486 v h) (hints_cons _ _ _ (der_25689 v h) (by intro d hd; cases hd)))
def cl_25697 : CNF.NClause := [(100,true),(42,false),(40,false),(33,true),(49,true),(58,true)]
theorem der_25697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25697 :=
  CNF.rup_sound cl_25697 [cl_2490,cl_25691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2490 v h) (hints_cons _ _ _ (der_25691 v h) (by intro d hd; cases hd)))
def cl_25698 : CNF.NClause := [(105,true),(41,false),(37,false),(50,false),(54,false),(60,false)]
theorem der_25698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25698 :=
  CNF.rup_sound cl_25698 [cl_2754,cl_23850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2754 v h) (hints_cons _ _ _ (der_23850 v h) (by intro d hd; cases hd)))
def cl_25699 : CNF.NClause := [(105,true),(41,false),(37,true),(50,false),(54,false),(60,false)]
theorem der_25699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25699 :=
  CNF.rup_sound cl_25699 [cl_2756,cl_24760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2756 v h) (hints_cons _ _ _ (der_24760 v h) (by intro d hd; cases hd)))
def cl_25700 : CNF.NClause := [(105,true),(60,false),(37,false),(50,false),(54,false),(33,true)]
theorem der_25700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25700 :=
  CNF.rup_sound cl_25700 [cl_2758,cl_25698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2758 v h) (hints_cons _ _ _ (der_25698 v h) (by intro d hd; cases hd)))
def cl_25701 : CNF.NClause := [(105,true),(50,false),(37,true),(41,true),(54,false),(60,false)]
theorem der_25701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25701 :=
  CNF.rup_sound cl_25701 [cl_2760,cl_24761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2760 v h) (hints_cons _ _ _ (der_24761 v h) (by intro d hd; cases hd)))
def cl_25702 : CNF.NClause := [(105,true),(41,false),(37,false),(33,true),(54,false),(60,false)]
theorem der_25702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25702 :=
  CNF.rup_sound cl_25702 [cl_2762,cl_25698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2762 v h) (hints_cons _ _ _ (der_25698 v h) (by intro d hd; cases hd)))
def cl_25703 : CNF.NClause := [(105,true),(41,false),(37,true),(50,true),(54,false),(60,false)]
theorem der_25703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25703 :=
  CNF.rup_sound cl_25703 [cl_2764,cl_24762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2764 v h) (hints_cons _ _ _ (der_24762 v h) (by intro d hd; cases hd)))
def cl_25704 : CNF.NClause := [(105,true),(60,false),(37,false),(41,true),(54,false),(33,true)]
theorem der_25704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25704 :=
  CNF.rup_sound cl_25704 [cl_2766,cl_25700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2766 v h) (hints_cons _ _ _ (der_25700 v h) (by intro d hd; cases hd)))
def cl_25705 : CNF.NClause := [(105,true),(60,false),(37,true),(33,true),(41,true),(54,false)]
theorem der_25705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25705 :=
  CNF.rup_sound cl_25705 [cl_2768,cl_25701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2768 v h) (hints_cons _ _ _ (der_25701 v h) (by intro d hd; cases hd)))
def cl_25706 : CNF.NClause := [(105,true),(41,false),(37,false),(33,true),(50,false),(60,false)]
theorem der_25706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25706 :=
  CNF.rup_sound cl_25706 [cl_2770,cl_25698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2770 v h) (hints_cons _ _ _ (der_25698 v h) (by intro d hd; cases hd)))
def cl_25707 : CNF.NClause := [(105,true),(41,false),(37,true),(50,false),(54,true),(60,false)]
theorem der_25707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25707 :=
  CNF.rup_sound cl_25707 [cl_2772,cl_24764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2772 v h) (hints_cons _ _ _ (der_24764 v h) (by intro d hd; cases hd)))
def cl_25708 : CNF.NClause := [(105,true),(60,false),(37,false),(41,true),(50,false),(33,true)]
theorem der_25708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25708 :=
  CNF.rup_sound cl_25708 [cl_2774,cl_25700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2774 v h) (hints_cons _ _ _ (der_25700 v h) (by intro d hd; cases hd)))
def cl_25709 : CNF.NClause := [(105,true),(37,true),(33,true),(50,false),(41,true),(60,false)]
theorem der_25709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25709 :=
  CNF.rup_sound cl_25709 [cl_2776,cl_25701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2776 v h) (hints_cons _ _ _ (der_25701 v h) (by intro d hd; cases hd)))
def cl_25710 : CNF.NClause := [(105,true),(41,false),(37,false),(33,true),(50,true),(60,false)]
theorem der_25710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25710 :=
  CNF.rup_sound cl_25710 [cl_2778,cl_25702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2778 v h) (hints_cons _ _ _ (der_25702 v h) (by intro d hd; cases hd)))
def cl_25711 : CNF.NClause := [(105,true),(41,false),(37,true),(33,true),(50,true),(60,false)]
theorem der_25711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25711 :=
  CNF.rup_sound cl_25711 [cl_2780,cl_25703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2780 v h) (hints_cons _ _ _ (der_25703 v h) (by intro d hd; cases hd)))
def cl_25712 : CNF.NClause := [(105,true),(60,false),(37,false),(41,true),(54,true),(33,true)]
theorem der_25712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25712 :=
  CNF.rup_sound cl_25712 [cl_2782,cl_25708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2782 v h) (hints_cons _ _ _ (der_25708 v h) (by intro d hd; cases hd)))
def cl_25713 : CNF.NClause := [(105,true),(41,false),(37,false),(50,false),(54,false),(60,true)]
theorem der_25713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25713 :=
  CNF.rup_sound cl_25713 [cl_2786,cl_2785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2786 v h) (hints_cons _ _ _ (inp_2785 v h) (by intro d hd; cases hd)))
def cl_25714 : CNF.NClause := [(105,true),(41,false),(37,true),(33,true),(50,false),(54,false)]
theorem der_25714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25714 :=
  CNF.rup_sound cl_25714 [cl_2788,cl_25699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2788 v h) (hints_cons _ _ _ (der_25699 v h) (by intro d hd; cases hd)))
def cl_25715 : CNF.NClause := [(105,true),(54,false),(37,false),(41,true),(50,false),(33,true)]
theorem der_25715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25715 :=
  CNF.rup_sound cl_25715 [cl_2790,cl_25700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2790 v h) (hints_cons _ _ _ (der_25700 v h) (by intro d hd; cases hd)))
def cl_25716 : CNF.NClause := [(105,true),(50,false),(37,true),(41,true),(33,true),(54,false)]
theorem der_25716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25716 :=
  CNF.rup_sound cl_25716 [cl_2792,cl_25701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2792 v h) (hints_cons _ _ _ (der_25701 v h) (by intro d hd; cases hd)))
def cl_25717 : CNF.NClause := [(105,true),(41,false),(37,false),(33,true),(50,true),(54,false)]
theorem der_25717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25717 :=
  CNF.rup_sound cl_25717 [cl_2794,cl_25702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2794 v h) (hints_cons _ _ _ (der_25702 v h) (by intro d hd; cases hd)))
def cl_25718 : CNF.NClause := [(105,true),(41,false),(37,true),(33,true),(50,true),(54,false)]
theorem der_25718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25718 :=
  CNF.rup_sound cl_25718 [cl_2796,cl_25703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2796 v h) (hints_cons _ _ _ (der_25703 v h) (by intro d hd; cases hd)))
def cl_25719 : CNF.NClause := [(105,true),(50,true),(37,false),(33,true),(54,false),(60,true)]
theorem der_25719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25719 :=
  CNF.rup_sound cl_25719 [cl_2798,cl_25717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2798 v h) (hints_cons _ _ _ (der_25717 v h) (by intro d hd; cases hd)))
def cl_25720 : CNF.NClause := [(105,true),(41,false),(37,false),(50,false),(54,true),(60,true)]
theorem der_25720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25720 :=
  CNF.rup_sound cl_25720 [cl_2802,cl_25060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2802 v h) (hints_cons _ _ _ (der_25060 v h) (by intro d hd; cases hd)))
def cl_25721 : CNF.NClause := [(105,true),(41,false),(37,true),(50,false),(54,true),(60,true)]
theorem der_25721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25721 :=
  CNF.rup_sound cl_25721 [cl_2804,cl_24772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2804 v h) (hints_cons _ _ _ (der_24772 v h) (by intro d hd; cases hd)))
def cl_25722 : CNF.NClause := [(105,true),(37,false),(33,true),(41,true),(50,false),(54,true)]
theorem der_25722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25722 :=
  CNF.rup_sound cl_25722 [cl_2806,cl_25712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2806 v h) (hints_cons _ _ _ (der_25712 v h) (by intro d hd; cases hd)))
def cl_25723 : CNF.NClause := [(105,true),(41,false),(37,false),(33,true),(50,true),(54,true)]
theorem der_25723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25723 :=
  CNF.rup_sound cl_25723 [cl_2810,cl_25710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2810 v h) (hints_cons _ _ _ (der_25710 v h) (by intro d hd; cases hd)))
def cl_25724 : CNF.NClause := [(110,true),(57,false),(46,false),(45,false),(52,false),(39,true)]
theorem der_25724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25724 :=
  CNF.rup_sound cl_25724 [cl_3076,cl_3075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3076 v h) (hints_cons _ _ _ (inp_3075 v h) (by intro d hd; cases hd)))
def cl_25725 : CNF.NClause := [(110,true),(52,false),(39,false),(46,false),(33,true),(57,false)]
theorem der_25725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25725 :=
  CNF.rup_sound cl_25725 [cl_3078,cl_3074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3078 v h) (hints_cons _ _ _ (inp_3074 v h) (by intro d hd; cases hd)))
def cl_25726 : CNF.NClause := [(110,true),(57,false),(39,true),(52,false),(46,false),(45,true)]
theorem der_25726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25726 :=
  CNF.rup_sound cl_25726 [cl_3080,cl_24708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3080 v h) (hints_cons _ _ _ (der_24708 v h) (by intro d hd; cases hd)))
def cl_25727 : CNF.NClause := [(110,true),(52,false),(39,false),(45,false),(33,true),(57,false)]
theorem der_25727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25727 :=
  CNF.rup_sound cl_25727 [cl_3082,cl_3074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3082 v h) (hints_cons _ _ _ (inp_3074 v h) (by intro d hd; cases hd)))
def cl_25728 : CNF.NClause := [(110,true),(46,true),(39,true),(45,false),(52,false),(57,false)]
theorem der_25728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25728 :=
  CNF.rup_sound cl_25728 [cl_3084,cl_24713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3084 v h) (hints_cons _ _ _ (der_24713 v h) (by intro d hd; cases hd)))
def cl_25729 : CNF.NClause := [(110,true),(52,false),(39,false),(45,true),(33,true),(57,false)]
theorem der_25729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25729 :=
  CNF.rup_sound cl_25729 [cl_3086,cl_25725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3086 v h) (hints_cons _ _ _ (der_25725 v h) (by intro d hd; cases hd)))
def cl_25730 : CNF.NClause := [(110,true),(39,true),(45,true),(52,false),(33,true),(57,false)]
theorem der_25730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25730 :=
  CNF.rup_sound cl_25730 [cl_3088,cl_25726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3088 v h) (hints_cons _ _ _ (der_25726 v h) (by intro d hd; cases hd)))
def cl_25731 : CNF.NClause := [(110,true),(46,false),(39,false),(45,false),(52,true),(57,false)]
theorem der_25731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25731 :=
  CNF.rup_sound cl_25731 [cl_3090,cl_3089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3090 v h) (hints_cons _ _ _ (inp_3089 v h) (by intro d hd; cases hd)))
def cl_25732 : CNF.NClause := [(110,true),(46,false),(45,false),(39,true),(33,true),(57,false)]
theorem der_25732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25732 :=
  CNF.rup_sound cl_25732 [cl_3092,cl_25724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3092 v h) (hints_cons _ _ _ (der_25724 v h) (by intro d hd; cases hd)))
def cl_25733 : CNF.NClause := [(110,true),(46,false),(39,false),(45,true),(52,true),(57,false)]
theorem der_25733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25733 :=
  CNF.rup_sound cl_25733 [cl_3094,cl_23799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3094 v h) (hints_cons _ _ _ (der_23799 v h) (by intro d hd; cases hd)))
def cl_25734 : CNF.NClause := [(110,true),(57,false),(46,false),(33,true),(45,true),(39,true)]
theorem der_25734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25734 :=
  CNF.rup_sound cl_25734 [cl_3096,cl_25726] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3096 v h) (hints_cons _ _ _ (der_25726 v h) (by intro d hd; cases hd)))
def cl_25735 : CNF.NClause := [(110,true),(57,false),(39,false),(45,false),(46,true),(52,true)]
theorem der_25735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25735 :=
  CNF.rup_sound cl_25735 [cl_3098,cl_25317] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3098 v h) (hints_cons _ _ _ (der_25317 v h) (by intro d hd; cases hd)))
def cl_25736 : CNF.NClause := [(110,true),(46,true),(39,true),(45,false),(52,true),(57,false)]
theorem der_25736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25736 :=
  CNF.rup_sound cl_25736 [cl_3100,cl_24713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3100 v h) (hints_cons _ _ _ (der_24713 v h) (by intro d hd; cases hd)))
def cl_25737 : CNF.NClause := [(110,true),(45,true),(39,false),(46,true),(52,true),(57,false)]
theorem der_25737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25737 :=
  CNF.rup_sound cl_25737 [cl_3102,cl_3101] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3102 v h) (hints_cons _ _ _ (inp_3101 v h) (by intro d hd; cases hd)))
def cl_25738 : CNF.NClause := [(110,true),(52,false),(39,false),(45,false),(46,false),(33,true)]
theorem der_25738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25738 :=
  CNF.rup_sound cl_25738 [cl_3106,cl_3074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3106 v h) (hints_cons _ _ _ (inp_3074 v h) (by intro d hd; cases hd)))
def cl_25739 : CNF.NClause := [(110,true),(45,false),(46,false),(39,true),(52,false),(33,true)]
theorem der_25739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25739 :=
  CNF.rup_sound cl_25739 [cl_3108,cl_25724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3108 v h) (hints_cons _ _ _ (der_25724 v h) (by intro d hd; cases hd)))
def cl_25740 : CNF.NClause := [(110,true),(52,false),(39,false),(45,true),(46,false),(33,true)]
theorem der_25740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25740 :=
  CNF.rup_sound cl_25740 [cl_3110,cl_25725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3110 v h) (hints_cons _ _ _ (der_25725 v h) (by intro d hd; cases hd)))
def cl_25741 : CNF.NClause := [(110,true),(46,false),(39,true),(45,true),(52,false),(57,true)]
theorem der_25741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25741 :=
  CNF.rup_sound cl_25741 [cl_3112,cl_24720] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3112 v h) (hints_cons _ _ _ (der_24720 v h) (by intro d hd; cases hd)))
def cl_25742 : CNF.NClause := [(110,true),(52,false),(39,false),(45,false),(46,true),(33,true)]
theorem der_25742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25742 :=
  CNF.rup_sound cl_25742 [cl_3114,cl_25727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3114 v h) (hints_cons _ _ _ (der_25727 v h) (by intro d hd; cases hd)))
def cl_25743 : CNF.NClause := [(110,true),(39,true),(52,false),(46,true),(33,true),(45,false)]
theorem der_25743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25743 :=
  CNF.rup_sound cl_25743 [cl_3116,cl_25728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3116 v h) (hints_cons _ _ _ (der_25728 v h) (by intro d hd; cases hd)))
def cl_25744 : CNF.NClause := [(110,true),(52,false),(39,false),(45,true),(33,true),(57,true)]
theorem der_25744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25744 :=
  CNF.rup_sound cl_25744 [cl_3118,cl_25740] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3118 v h) (hints_cons _ _ _ (der_25740 v h) (by intro d hd; cases hd)))
def cl_25745 : CNF.NClause := [(110,true),(46,false),(39,false),(45,false),(33,true),(52,true)]
theorem der_25745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25745 :=
  CNF.rup_sound cl_25745 [cl_3122,cl_25731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3122 v h) (hints_cons _ _ _ (der_25731 v h) (by intro d hd; cases hd)))
def cl_25746 : CNF.NClause := [(110,true),(57,true),(46,false),(45,false),(33,true),(39,true)]
theorem der_25746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25746 :=
  CNF.rup_sound cl_25746 [cl_3124,cl_25739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3124 v h) (hints_cons _ _ _ (der_25739 v h) (by intro d hd; cases hd)))
def cl_25747 : CNF.NClause := [(110,true),(39,false),(33,true),(46,false),(52,true),(57,true)]
theorem der_25747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25747 :=
  CNF.rup_sound cl_25747 [cl_3126,cl_25745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3126 v h) (hints_cons _ _ _ (der_25745 v h) (by intro d hd; cases hd)))
def cl_25748 : CNF.NClause := [(110,true),(39,false),(33,true),(45,false),(46,true),(57,true)]
theorem der_25748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25748 :=
  CNF.rup_sound cl_25748 [cl_3130,cl_25742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3130 v h) (hints_cons _ _ _ (der_25742 v h) (by intro d hd; cases hd)))
def cl_25749 : CNF.NClause := [(110,false),(45,true),(57,true),(46,true),(33,true),(52,true)]
theorem der_25749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_25749 :=
  CNF.rup_sound cl_25749 [cl_3134,cl_23937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3134 v h) (hints_cons _ _ _ (der_23937 v h) (by intro d hd; cases hd)))
def chunk006 : List CNF.NClause := [cl_25204,cl_25205,cl_25206,cl_25207,cl_25208,cl_25209,cl_25211,cl_25212,cl_25213,cl_25214,cl_25215,cl_25217,cl_25219,cl_25220,cl_25223,cl_25226,cl_25227,cl_25228,cl_25229,cl_25230,cl_25232,cl_25233,cl_25234,cl_25235,cl_25236,cl_25237,cl_25241,cl_25242,cl_25243,cl_25244,cl_25245,cl_25246,cl_25249,cl_25250,cl_25251,cl_25252,cl_25253,cl_25257,cl_25258,cl_25259,cl_25260,cl_25261,cl_25262,cl_25263,cl_25264,cl_25265,cl_25266,cl_25267,cl_25268,cl_25269,cl_25270,cl_25271,cl_25272,cl_25273,cl_25274,cl_25275,cl_25276,cl_25277,cl_25278,cl_25279,cl_25280,cl_25281,cl_25282,cl_25283,cl_25284,cl_25285,cl_25286,cl_25287,cl_25288,cl_25289,cl_25290,cl_25291,cl_25292,cl_25293,cl_25294,cl_25295,cl_25296,cl_25297,cl_25298,cl_25299,cl_25300,cl_25301,cl_25302,cl_25304,cl_25305,cl_25306,cl_25307,cl_25308,cl_25309,cl_25310,cl_25311,cl_25312,cl_25313,cl_25314,cl_25315,cl_25316,cl_25317,cl_25318,cl_25319,cl_25320,cl_25321,cl_25322,cl_25323,cl_25324,cl_25325,cl_25326,cl_25327,cl_25328,cl_25329,cl_25331,cl_25332,cl_25333,cl_25334,cl_25335,cl_25336,cl_25337,cl_25338,cl_25339,cl_25340,cl_25341,cl_25342,cl_25343,cl_25344,cl_25345,cl_25346,cl_25347,cl_25348,cl_25349,cl_25350,cl_25351,cl_25352,cl_25353,cl_25354,cl_25355,cl_25356,cl_25357,cl_25358,cl_25359,cl_25360,cl_25361,cl_25362,cl_25363,cl_25364,cl_25365,cl_25366,cl_25367,cl_25368,cl_25369,cl_25370,cl_25371,cl_25372,cl_25373,cl_25374,cl_25375,cl_25376,cl_25378,cl_25380,cl_25382,cl_25383,cl_25384,cl_25385,cl_25386,cl_25387,cl_25388,cl_25389,cl_25390,cl_25391,cl_25392,cl_25393,cl_25394,cl_25395,cl_25396,cl_25397,cl_25398,cl_25399,cl_25400,cl_25401,cl_25402,cl_25403,cl_25404,cl_25405,cl_25406,cl_25407,cl_25408,cl_25409,cl_25410,cl_25411,cl_25412,cl_25413,cl_25414,cl_25415,cl_25416,cl_25417,cl_25418,cl_25419,cl_25420,cl_25421,cl_25422,cl_25423,cl_25424,cl_25425,cl_25426,cl_25427,cl_25428,cl_25429,cl_25430,cl_25431,cl_25432,cl_25433,cl_25434,cl_25435,cl_25436,cl_25437,cl_25438,cl_25439,cl_25440,cl_25441,cl_25442,cl_25443,cl_25444,cl_25445,cl_25446,cl_25447,cl_25448,cl_25449,cl_25450,cl_25451,cl_25452,cl_25453,cl_25454,cl_25455,cl_25456,cl_25457,cl_25458,cl_25459,cl_25460,cl_25461,cl_25462,cl_25463,cl_25464,cl_25465,cl_25466,cl_25467,cl_25468,cl_25469,cl_25470,cl_25471,cl_25472,cl_25473,cl_25474,cl_25475,cl_25476,cl_25477,cl_25478,cl_25479,cl_25480,cl_25481,cl_25482,cl_25483,cl_25484,cl_25485,cl_25486,cl_25487,cl_25488,cl_25489,cl_25490,cl_25491,cl_25492,cl_25493,cl_25494,cl_25495,cl_25496,cl_25497,cl_25498,cl_25499,cl_25500,cl_25501,cl_25502,cl_25504,cl_25505,cl_25506,cl_25507,cl_25508,cl_25509,cl_25510,cl_25511,cl_25512,cl_25513,cl_25514,cl_25515,cl_25516,cl_25517,cl_25518,cl_25519,cl_25520,cl_25521,cl_25522,cl_25523,cl_25524,cl_25525,cl_25526,cl_25527,cl_25528,cl_25529,cl_25530,cl_25531,cl_25532,cl_25533,cl_25534,cl_25535,cl_25536,cl_25537,cl_25538,cl_25540,cl_25542,cl_25544,cl_25546,cl_25547,cl_25548,cl_25549,cl_25550,cl_25551,cl_25552,cl_25554,cl_25556,cl_25558,cl_25561,cl_25562,cl_25563,cl_25564,cl_25567,cl_25569,cl_25570,cl_25571,cl_25572,cl_25574,cl_25576,cl_25577,cl_25578,cl_25579,cl_25580,cl_25582,cl_25583,cl_25584,cl_25587,cl_25588,cl_25589,cl_25590,cl_25591,cl_25592,cl_25594,cl_25596,cl_25597,cl_25598,cl_25599,cl_25600,cl_25601,cl_25602,cl_25603,cl_25604,cl_25605,cl_25606,cl_25607,cl_25608,cl_25609,cl_25610,cl_25611,cl_25612,cl_25613,cl_25614,cl_25615,cl_25616,cl_25617,cl_25618,cl_25619,cl_25620,cl_25621,cl_25622,cl_25623,cl_25624,cl_25625,cl_25626,cl_25627,cl_25628,cl_25629,cl_25630,cl_25631,cl_25632,cl_25633,cl_25634,cl_25635,cl_25636,cl_25637,cl_25638,cl_25639,cl_25640,cl_25641,cl_25642,cl_25643,cl_25644,cl_25645,cl_25646,cl_25647,cl_25648,cl_25649,cl_25651,cl_25652,cl_25653,cl_25655,cl_25656,cl_25657,cl_25660,cl_25662,cl_25663,cl_25664,cl_25665,cl_25666,cl_25667,cl_25668,cl_25669,cl_25670,cl_25671,cl_25672,cl_25673,cl_25674,cl_25675,cl_25676,cl_25677,cl_25678,cl_25679,cl_25680,cl_25681,cl_25682,cl_25683,cl_25684,cl_25685,cl_25686,cl_25687,cl_25688,cl_25689,cl_25690,cl_25691,cl_25692,cl_25693,cl_25694,cl_25695,cl_25696,cl_25697,cl_25698,cl_25699,cl_25700,cl_25701,cl_25702,cl_25703,cl_25704,cl_25705,cl_25706,cl_25707,cl_25708,cl_25709,cl_25710,cl_25711,cl_25712,cl_25713,cl_25714,cl_25715,cl_25716,cl_25717,cl_25718,cl_25719,cl_25720,cl_25721,cl_25722,cl_25723,cl_25724,cl_25725,cl_25726,cl_25727,cl_25728,cl_25729,cl_25730,cl_25731,cl_25732,cl_25733,cl_25734,cl_25735,cl_25736,cl_25737,cl_25738,cl_25739,cl_25740,cl_25741,cl_25742,cl_25743,cl_25744,cl_25745,cl_25746,cl_25747,cl_25748,cl_25749]
theorem chunk_sound006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk006, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_25204 v h) (hints_cons _ _ _ (der_25205 v h) (hints_cons _ _ _ (der_25206 v h) (hints_cons _ _ _ (der_25207 v h) (hints_cons _ _ _ (der_25208 v h) (hints_cons _ _ _ (der_25209 v h) (hints_cons _ _ _ (der_25211 v h) (hints_cons _ _ _ (der_25212 v h) (hints_cons _ _ _ (der_25213 v h) (hints_cons _ _ _ (der_25214 v h) (hints_cons _ _ _ (der_25215 v h) (hints_cons _ _ _ (der_25217 v h) (hints_cons _ _ _ (der_25219 v h) (hints_cons _ _ _ (der_25220 v h) (hints_cons _ _ _ (der_25223 v h) (hints_cons _ _ _ (der_25226 v h) (hints_cons _ _ _ (der_25227 v h) (hints_cons _ _ _ (der_25228 v h) (hints_cons _ _ _ (der_25229 v h) (hints_cons _ _ _ (der_25230 v h) (hints_cons _ _ _ (der_25232 v h) (hints_cons _ _ _ (der_25233 v h) (hints_cons _ _ _ (der_25234 v h) (hints_cons _ _ _ (der_25235 v h) (hints_cons _ _ _ (der_25236 v h) (hints_cons _ _ _ (der_25237 v h) (hints_cons _ _ _ (der_25241 v h) (hints_cons _ _ _ (der_25242 v h) (hints_cons _ _ _ (der_25243 v h) (hints_cons _ _ _ (der_25244 v h) (hints_cons _ _ _ (der_25245 v h) (hints_cons _ _ _ (der_25246 v h) (hints_cons _ _ _ (der_25249 v h) (hints_cons _ _ _ (der_25250 v h) (hints_cons _ _ _ (der_25251 v h) (hints_cons _ _ _ (der_25252 v h) (hints_cons _ _ _ (der_25253 v h) (hints_cons _ _ _ (der_25257 v h) (hints_cons _ _ _ (der_25258 v h) (hints_cons _ _ _ (der_25259 v h) (hints_cons _ _ _ (der_25260 v h) (hints_cons _ _ _ (der_25261 v h) (hints_cons _ _ _ (der_25262 v h) (hints_cons _ _ _ (der_25263 v h) (hints_cons _ _ _ (der_25264 v h) (hints_cons _ _ _ (der_25265 v h) (hints_cons _ _ _ (der_25266 v h) (hints_cons _ _ _ (der_25267 v h) (hints_cons _ _ _ (der_25268 v h) (hints_cons _ _ _ (der_25269 v h) (hints_cons _ _ _ (der_25270 v h) (hints_cons _ _ _ (der_25271 v h) (hints_cons _ _ _ (der_25272 v h) (hints_cons _ _ _ (der_25273 v h) (hints_cons _ _ _ (der_25274 v h) (hints_cons _ _ _ (der_25275 v h) (hints_cons _ _ _ (der_25276 v h) (hints_cons _ _ _ (der_25277 v h) (hints_cons _ _ _ (der_25278 v h) (hints_cons _ _ _ (der_25279 v h) (hints_cons _ _ _ (der_25280 v h) (hints_cons _ _ _ (der_25281 v h) (hints_cons _ _ _ (der_25282 v h) (hints_cons _ _ _ (der_25283 v h) (hints_cons _ _ _ (der_25284 v h) (hints_cons _ _ _ (der_25285 v h) (hints_cons _ _ _ (der_25286 v h) (hints_cons _ _ _ (der_25287 v h) (hints_cons _ _ _ (der_25288 v h) (hints_cons _ _ _ (der_25289 v h) (hints_cons _ _ _ (der_25290 v h) (hints_cons _ _ _ (der_25291 v h) (hints_cons _ _ _ (der_25292 v h) (hints_cons _ _ _ (der_25293 v h) (hints_cons _ _ _ (der_25294 v h) (hints_cons _ _ _ (der_25295 v h) (hints_cons _ _ _ (der_25296 v h) (hints_cons _ _ _ (der_25297 v h) (hints_cons _ _ _ (der_25298 v h) (hints_cons _ _ _ (der_25299 v h) (hints_cons _ _ _ (der_25300 v h) (hints_cons _ _ _ (der_25301 v h) (hints_cons _ _ _ (der_25302 v h) (hints_cons _ _ _ (der_25304 v h) (hints_cons _ _ _ (der_25305 v h) (hints_cons _ _ _ (der_25306 v h) (hints_cons _ _ _ (der_25307 v h) (hints_cons _ _ _ (der_25308 v h) (hints_cons _ _ _ (der_25309 v h) (hints_cons _ _ _ (der_25310 v h) (hints_cons _ _ _ (der_25311 v h) (hints_cons _ _ _ (der_25312 v h) (hints_cons _ _ _ (der_25313 v h) (hints_cons _ _ _ (der_25314 v h) (hints_cons _ _ _ (der_25315 v h) (hints_cons _ _ _ (der_25316 v h) (hints_cons _ _ _ (der_25317 v h) (hints_cons _ _ _ (der_25318 v h) (hints_cons _ _ _ (der_25319 v h) (hints_cons _ _ _ (der_25320 v h) (hints_cons _ _ _ (der_25321 v h) (hints_cons _ _ _ (der_25322 v h) (hints_cons _ _ _ (der_25323 v h) (hints_cons _ _ _ (der_25324 v h) (hints_cons _ _ _ (der_25325 v h) (hints_cons _ _ _ (der_25326 v h) (hints_cons _ _ _ (der_25327 v h) (hints_cons _ _ _ (der_25328 v h) (hints_cons _ _ _ (der_25329 v h) (hints_cons _ _ _ (der_25331 v h) (hints_cons _ _ _ (der_25332 v h) (hints_cons _ _ _ (der_25333 v h) (hints_cons _ _ _ (der_25334 v h) (hints_cons _ _ _ (der_25335 v h) (hints_cons _ _ _ (der_25336 v h) (hints_cons _ _ _ (der_25337 v h) (hints_cons _ _ _ (der_25338 v h) (hints_cons _ _ _ (der_25339 v h) (hints_cons _ _ _ (der_25340 v h) (hints_cons _ _ _ (der_25341 v h) (hints_cons _ _ _ (der_25342 v h) (hints_cons _ _ _ (der_25343 v h) (hints_cons _ _ _ (der_25344 v h) (hints_cons _ _ _ (der_25345 v h) (hints_cons _ _ _ (der_25346 v h) (hints_cons _ _ _ (der_25347 v h) (hints_cons _ _ _ (der_25348 v h) (hints_cons _ _ _ (der_25349 v h) (hints_cons _ _ _ (der_25350 v h) (hints_cons _ _ _ (der_25351 v h) (hints_cons _ _ _ (der_25352 v h) (hints_cons _ _ _ (der_25353 v h) (hints_cons _ _ _ (der_25354 v h) (hints_cons _ _ _ (der_25355 v h) (hints_cons _ _ _ (der_25356 v h) (hints_cons _ _ _ (der_25357 v h) (hints_cons _ _ _ (der_25358 v h) (hints_cons _ _ _ (der_25359 v h) (hints_cons _ _ _ (der_25360 v h) (hints_cons _ _ _ (der_25361 v h) (hints_cons _ _ _ (der_25362 v h) (hints_cons _ _ _ (der_25363 v h) (hints_cons _ _ _ (der_25364 v h) (hints_cons _ _ _ (der_25365 v h) (hints_cons _ _ _ (der_25366 v h) (hints_cons _ _ _ (der_25367 v h) (hints_cons _ _ _ (der_25368 v h) (hints_cons _ _ _ (der_25369 v h) (hints_cons _ _ _ (der_25370 v h) (hints_cons _ _ _ (der_25371 v h) (hints_cons _ _ _ (der_25372 v h) (hints_cons _ _ _ (der_25373 v h) (hints_cons _ _ _ (der_25374 v h) (hints_cons _ _ _ (der_25375 v h) (hints_cons _ _ _ (der_25376 v h) (hints_cons _ _ _ (der_25378 v h) (hints_cons _ _ _ (der_25380 v h) (hints_cons _ _ _ (der_25382 v h) (hints_cons _ _ _ (der_25383 v h) (hints_cons _ _ _ (der_25384 v h) (hints_cons _ _ _ (der_25385 v h) (hints_cons _ _ _ (der_25386 v h) (hints_cons _ _ _ (der_25387 v h) (hints_cons _ _ _ (der_25388 v h) (hints_cons _ _ _ (der_25389 v h) (hints_cons _ _ _ (der_25390 v h) (hints_cons _ _ _ (der_25391 v h) (hints_cons _ _ _ (der_25392 v h) (hints_cons _ _ _ (der_25393 v h) (hints_cons _ _ _ (der_25394 v h) (hints_cons _ _ _ (der_25395 v h) (hints_cons _ _ _ (der_25396 v h) (hints_cons _ _ _ (der_25397 v h) (hints_cons _ _ _ (der_25398 v h) (hints_cons _ _ _ (der_25399 v h) (hints_cons _ _ _ (der_25400 v h) (hints_cons _ _ _ (der_25401 v h) (hints_cons _ _ _ (der_25402 v h) (hints_cons _ _ _ (der_25403 v h) (hints_cons _ _ _ (der_25404 v h) (hints_cons _ _ _ (der_25405 v h) (hints_cons _ _ _ (der_25406 v h) (hints_cons _ _ _ (der_25407 v h) (hints_cons _ _ _ (der_25408 v h) (hints_cons _ _ _ (der_25409 v h) (hints_cons _ _ _ (der_25410 v h) (hints_cons _ _ _ (der_25411 v h) (hints_cons _ _ _ (der_25412 v h) (hints_cons _ _ _ (der_25413 v h) (hints_cons _ _ _ (der_25414 v h) (hints_cons _ _ _ (der_25415 v h) (hints_cons _ _ _ (der_25416 v h) (hints_cons _ _ _ (der_25417 v h) (hints_cons _ _ _ (der_25418 v h) (hints_cons _ _ _ (der_25419 v h) (hints_cons _ _ _ (der_25420 v h) (hints_cons _ _ _ (der_25421 v h) (hints_cons _ _ _ (der_25422 v h) (hints_cons _ _ _ (der_25423 v h) (hints_cons _ _ _ (der_25424 v h) (hints_cons _ _ _ (der_25425 v h) (hints_cons _ _ _ (der_25426 v h) (hints_cons _ _ _ (der_25427 v h) (hints_cons _ _ _ (der_25428 v h) (hints_cons _ _ _ (der_25429 v h) (hints_cons _ _ _ (der_25430 v h) (hints_cons _ _ _ (der_25431 v h) (hints_cons _ _ _ (der_25432 v h) (hints_cons _ _ _ (der_25433 v h) (hints_cons _ _ _ (der_25434 v h) (hints_cons _ _ _ (der_25435 v h) (hints_cons _ _ _ (der_25436 v h) (hints_cons _ _ _ (der_25437 v h) (hints_cons _ _ _ (der_25438 v h) (hints_cons _ _ _ (der_25439 v h) (hints_cons _ _ _ (der_25440 v h) (hints_cons _ _ _ (der_25441 v h) (hints_cons _ _ _ (der_25442 v h) (hints_cons _ _ _ (der_25443 v h) (hints_cons _ _ _ (der_25444 v h) (hints_cons _ _ _ (der_25445 v h) (hints_cons _ _ _ (der_25446 v h) (hints_cons _ _ _ (der_25447 v h) (hints_cons _ _ _ (der_25448 v h) (hints_cons _ _ _ (der_25449 v h) (hints_cons _ _ _ (der_25450 v h) (hints_cons _ _ _ (der_25451 v h) (hints_cons _ _ _ (der_25452 v h) (hints_cons _ _ _ (der_25453 v h) (hints_cons _ _ _ (der_25454 v h) (hints_cons _ _ _ (der_25455 v h) (hints_cons _ _ _ (der_25456 v h) (hints_cons _ _ _ (der_25457 v h) (hints_cons _ _ _ (der_25458 v h) (hints_cons _ _ _ (der_25459 v h) (hints_cons _ _ _ (der_25460 v h) (hints_cons _ _ _ (der_25461 v h) (hints_cons _ _ _ (der_25462 v h) (hints_cons _ _ _ (der_25463 v h) (hints_cons _ _ _ (der_25464 v h) (hints_cons _ _ _ (der_25465 v h) (hints_cons _ _ _ (der_25466 v h) (hints_cons _ _ _ (der_25467 v h) (hints_cons _ _ _ (der_25468 v h) (hints_cons _ _ _ (der_25469 v h) (hints_cons _ _ _ (der_25470 v h) (hints_cons _ _ _ (der_25471 v h) (hints_cons _ _ _ (der_25472 v h) (hints_cons _ _ _ (der_25473 v h) (hints_cons _ _ _ (der_25474 v h) (hints_cons _ _ _ (der_25475 v h) (hints_cons _ _ _ (der_25476 v h) (hints_cons _ _ _ (der_25477 v h) (hints_cons _ _ _ (der_25478 v h) (hints_cons _ _ _ (der_25479 v h) (hints_cons _ _ _ (der_25480 v h) (hints_cons _ _ _ (der_25481 v h) (hints_cons _ _ _ (der_25482 v h) (hints_cons _ _ _ (der_25483 v h) (hints_cons _ _ _ (der_25484 v h) (hints_cons _ _ _ (der_25485 v h) (hints_cons _ _ _ (der_25486 v h) (hints_cons _ _ _ (der_25487 v h) (hints_cons _ _ _ (der_25488 v h) (hints_cons _ _ _ (der_25489 v h) (hints_cons _ _ _ (der_25490 v h) (hints_cons _ _ _ (der_25491 v h) (hints_cons _ _ _ (der_25492 v h) (hints_cons _ _ _ (der_25493 v h) (hints_cons _ _ _ (der_25494 v h) (hints_cons _ _ _ (der_25495 v h) (hints_cons _ _ _ (der_25496 v h) (hints_cons _ _ _ (der_25497 v h) (hints_cons _ _ _ (der_25498 v h) (hints_cons _ _ _ (der_25499 v h) (hints_cons _ _ _ (der_25500 v h) (hints_cons _ _ _ (der_25501 v h) (hints_cons _ _ _ (der_25502 v h) (hints_cons _ _ _ (der_25504 v h) (hints_cons _ _ _ (der_25505 v h) (hints_cons _ _ _ (der_25506 v h) (hints_cons _ _ _ (der_25507 v h) (hints_cons _ _ _ (der_25508 v h) (hints_cons _ _ _ (der_25509 v h) (hints_cons _ _ _ (der_25510 v h) (hints_cons _ _ _ (der_25511 v h) (hints_cons _ _ _ (der_25512 v h) (hints_cons _ _ _ (der_25513 v h) (hints_cons _ _ _ (der_25514 v h) (hints_cons _ _ _ (der_25515 v h) (hints_cons _ _ _ (der_25516 v h) (hints_cons _ _ _ (der_25517 v h) (hints_cons _ _ _ (der_25518 v h) (hints_cons _ _ _ (der_25519 v h) (hints_cons _ _ _ (der_25520 v h) (hints_cons _ _ _ (der_25521 v h) (hints_cons _ _ _ (der_25522 v h) (hints_cons _ _ _ (der_25523 v h) (hints_cons _ _ _ (der_25524 v h) (hints_cons _ _ _ (der_25525 v h) (hints_cons _ _ _ (der_25526 v h) (hints_cons _ _ _ (der_25527 v h) (hints_cons _ _ _ (der_25528 v h) (hints_cons _ _ _ (der_25529 v h) (hints_cons _ _ _ (der_25530 v h) (hints_cons _ _ _ (der_25531 v h) (hints_cons _ _ _ (der_25532 v h) (hints_cons _ _ _ (der_25533 v h) (hints_cons _ _ _ (der_25534 v h) (hints_cons _ _ _ (der_25535 v h) (hints_cons _ _ _ (der_25536 v h) (hints_cons _ _ _ (der_25537 v h) (hints_cons _ _ _ (der_25538 v h) (hints_cons _ _ _ (der_25540 v h) (hints_cons _ _ _ (der_25542 v h) (hints_cons _ _ _ (der_25544 v h) (hints_cons _ _ _ (der_25546 v h) (hints_cons _ _ _ (der_25547 v h) (hints_cons _ _ _ (der_25548 v h) (hints_cons _ _ _ (der_25549 v h) (hints_cons _ _ _ (der_25550 v h) (hints_cons _ _ _ (der_25551 v h) (hints_cons _ _ _ (der_25552 v h) (hints_cons _ _ _ (der_25554 v h) (hints_cons _ _ _ (der_25556 v h) (hints_cons _ _ _ (der_25558 v h) (hints_cons _ _ _ (der_25561 v h) (hints_cons _ _ _ (der_25562 v h) (hints_cons _ _ _ (der_25563 v h) (hints_cons _ _ _ (der_25564 v h) (hints_cons _ _ _ (der_25567 v h) (hints_cons _ _ _ (der_25569 v h) (hints_cons _ _ _ (der_25570 v h) (hints_cons _ _ _ (der_25571 v h) (hints_cons _ _ _ (der_25572 v h) (hints_cons _ _ _ (der_25574 v h) (hints_cons _ _ _ (der_25576 v h) (hints_cons _ _ _ (der_25577 v h) (hints_cons _ _ _ (der_25578 v h) (hints_cons _ _ _ (der_25579 v h) (hints_cons _ _ _ (der_25580 v h) (hints_cons _ _ _ (der_25582 v h) (hints_cons _ _ _ (der_25583 v h) (hints_cons _ _ _ (der_25584 v h) (hints_cons _ _ _ (der_25587 v h) (hints_cons _ _ _ (der_25588 v h) (hints_cons _ _ _ (der_25589 v h) (hints_cons _ _ _ (der_25590 v h) (hints_cons _ _ _ (der_25591 v h) (hints_cons _ _ _ (der_25592 v h) (hints_cons _ _ _ (der_25594 v h) (hints_cons _ _ _ (der_25596 v h) (hints_cons _ _ _ (der_25597 v h) (hints_cons _ _ _ (der_25598 v h) (hints_cons _ _ _ (der_25599 v h) (hints_cons _ _ _ (der_25600 v h) (hints_cons _ _ _ (der_25601 v h) (hints_cons _ _ _ (der_25602 v h) (hints_cons _ _ _ (der_25603 v h) (hints_cons _ _ _ (der_25604 v h) (hints_cons _ _ _ (der_25605 v h) (hints_cons _ _ _ (der_25606 v h) (hints_cons _ _ _ (der_25607 v h) (hints_cons _ _ _ (der_25608 v h) (hints_cons _ _ _ (der_25609 v h) (hints_cons _ _ _ (der_25610 v h) (hints_cons _ _ _ (der_25611 v h) (hints_cons _ _ _ (der_25612 v h) (hints_cons _ _ _ (der_25613 v h) (hints_cons _ _ _ (der_25614 v h) (hints_cons _ _ _ (der_25615 v h) (hints_cons _ _ _ (der_25616 v h) (hints_cons _ _ _ (der_25617 v h) (hints_cons _ _ _ (der_25618 v h) (hints_cons _ _ _ (der_25619 v h) (hints_cons _ _ _ (der_25620 v h) (hints_cons _ _ _ (der_25621 v h) (hints_cons _ _ _ (der_25622 v h) (hints_cons _ _ _ (der_25623 v h) (hints_cons _ _ _ (der_25624 v h) (hints_cons _ _ _ (der_25625 v h) (hints_cons _ _ _ (der_25626 v h) (hints_cons _ _ _ (der_25627 v h) (hints_cons _ _ _ (der_25628 v h) (hints_cons _ _ _ (der_25629 v h) (hints_cons _ _ _ (der_25630 v h) (hints_cons _ _ _ (der_25631 v h) (hints_cons _ _ _ (der_25632 v h) (hints_cons _ _ _ (der_25633 v h) (hints_cons _ _ _ (der_25634 v h) (hints_cons _ _ _ (der_25635 v h) (hints_cons _ _ _ (der_25636 v h) (hints_cons _ _ _ (der_25637 v h) (hints_cons _ _ _ (der_25638 v h) (hints_cons _ _ _ (der_25639 v h) (hints_cons _ _ _ (der_25640 v h) (hints_cons _ _ _ (der_25641 v h) (hints_cons _ _ _ (der_25642 v h) (hints_cons _ _ _ (der_25643 v h) (hints_cons _ _ _ (der_25644 v h) (hints_cons _ _ _ (der_25645 v h) (hints_cons _ _ _ (der_25646 v h) (hints_cons _ _ _ (der_25647 v h) (hints_cons _ _ _ (der_25648 v h) (hints_cons _ _ _ (der_25649 v h) (hints_cons _ _ _ (der_25651 v h) (hints_cons _ _ _ (der_25652 v h) (hints_cons _ _ _ (der_25653 v h) (hints_cons _ _ _ (der_25655 v h) (hints_cons _ _ _ (der_25656 v h) (hints_cons _ _ _ (der_25657 v h) (hints_cons _ _ _ (der_25660 v h) (hints_cons _ _ _ (der_25662 v h) (hints_cons _ _ _ (der_25663 v h) (hints_cons _ _ _ (der_25664 v h) (hints_cons _ _ _ (der_25665 v h) (hints_cons _ _ _ (der_25666 v h) (hints_cons _ _ _ (der_25667 v h) (hints_cons _ _ _ (der_25668 v h) (hints_cons _ _ _ (der_25669 v h) (hints_cons _ _ _ (der_25670 v h) (hints_cons _ _ _ (der_25671 v h) (hints_cons _ _ _ (der_25672 v h) (hints_cons _ _ _ (der_25673 v h) (hints_cons _ _ _ (der_25674 v h) (hints_cons _ _ _ (der_25675 v h) (hints_cons _ _ _ (der_25676 v h) (hints_cons _ _ _ (der_25677 v h) (hints_cons _ _ _ (der_25678 v h) (hints_cons _ _ _ (der_25679 v h) (hints_cons _ _ _ (der_25680 v h) (hints_cons _ _ _ (der_25681 v h) (hints_cons _ _ _ (der_25682 v h) (hints_cons _ _ _ (der_25683 v h) (hints_cons _ _ _ (der_25684 v h) (hints_cons _ _ _ (der_25685 v h) (hints_cons _ _ _ (der_25686 v h) (hints_cons _ _ _ (der_25687 v h) (hints_cons _ _ _ (der_25688 v h) (hints_cons _ _ _ (der_25689 v h) (hints_cons _ _ _ (der_25690 v h) (hints_cons _ _ _ (der_25691 v h) (hints_cons _ _ _ (der_25692 v h) (hints_cons _ _ _ (der_25693 v h) (hints_cons _ _ _ (der_25694 v h) (hints_cons _ _ _ (der_25695 v h) (hints_cons _ _ _ (der_25696 v h) (hints_cons _ _ _ (der_25697 v h) (hints_cons _ _ _ (der_25698 v h) (hints_cons _ _ _ (der_25699 v h) (hints_cons _ _ _ (der_25700 v h) (hints_cons _ _ _ (der_25701 v h) (hints_cons _ _ _ (der_25702 v h) (hints_cons _ _ _ (der_25703 v h) (hints_cons _ _ _ (der_25704 v h) (hints_cons _ _ _ (der_25705 v h) (hints_cons _ _ _ (der_25706 v h) (hints_cons _ _ _ (der_25707 v h) (hints_cons _ _ _ (der_25708 v h) (hints_cons _ _ _ (der_25709 v h) (hints_cons _ _ _ (der_25710 v h) (hints_cons _ _ _ (der_25711 v h) (hints_cons _ _ _ (der_25712 v h) (hints_cons _ _ _ (der_25713 v h) (hints_cons _ _ _ (der_25714 v h) (hints_cons _ _ _ (der_25715 v h) (hints_cons _ _ _ (der_25716 v h) (hints_cons _ _ _ (der_25717 v h) (hints_cons _ _ _ (der_25718 v h) (hints_cons _ _ _ (der_25719 v h) (hints_cons _ _ _ (der_25720 v h) (hints_cons _ _ _ (der_25721 v h) (hints_cons _ _ _ (der_25722 v h) (hints_cons _ _ _ (der_25723 v h) (hints_cons _ _ _ (der_25724 v h) (hints_cons _ _ _ (der_25725 v h) (hints_cons _ _ _ (der_25726 v h) (hints_cons _ _ _ (der_25727 v h) (hints_cons _ _ _ (der_25728 v h) (hints_cons _ _ _ (der_25729 v h) (hints_cons _ _ _ (der_25730 v h) (hints_cons _ _ _ (der_25731 v h) (hints_cons _ _ _ (der_25732 v h) (hints_cons _ _ _ (der_25733 v h) (hints_cons _ _ _ (der_25734 v h) (hints_cons _ _ _ (der_25735 v h) (hints_cons _ _ _ (der_25736 v h) (hints_cons _ _ _ (der_25737 v h) (hints_cons _ _ _ (der_25738 v h) (hints_cons _ _ _ (der_25739 v h) (hints_cons _ _ _ (der_25740 v h) (hints_cons _ _ _ (der_25741 v h) (hints_cons _ _ _ (der_25742 v h) (hints_cons _ _ _ (der_25743 v h) (hints_cons _ _ _ (der_25744 v h) (hints_cons _ _ _ (der_25745 v h) (hints_cons _ _ _ (der_25746 v h) (hints_cons _ _ _ (der_25747 v h) (hints_cons _ _ _ (der_25748 v h) (hints_cons _ _ _ (der_25749 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix006 := prefix005 ++ chunk006
theorem prefix_sound006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix006, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound005 v h c hc
  · exact chunk_sound006 v h c hc
end Percolation.NReplay
