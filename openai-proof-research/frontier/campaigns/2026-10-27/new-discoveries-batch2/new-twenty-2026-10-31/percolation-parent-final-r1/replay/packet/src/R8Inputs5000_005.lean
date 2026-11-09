import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4107 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,true),(81,false),(86,false),(87,false)]
theorem inputList4107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4107 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4107 (by decide) v hb
mask_input "4107|234533970188479499010572290|75631650702209161625600"
def inputClause4108 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(81,false),(86,false),(87,false)]
theorem inputList4108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4108 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4108 (by decide) v hb
mask_input "4108|234533970188479499010572288|75631650702209161625602"
def inputClause4109 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,false),(86,false),(87,false)]
theorem inputList4109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4109 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4109 (by decide) v hb
mask_input "4109|234531682792214359026171906|77919046967349146025984"
def inputClause4110 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,false),(86,false),(87,false)]
theorem inputList4110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4110 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4110 (by decide) v hb
mask_input "4110|234531682792214359026171904|77919046967349146025986"
def inputClause4111 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,false),(86,false),(87,false)]
theorem inputList4111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4111 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4111 (by decide) v hb
mask_input "4111|234531609005238064187965442|77992833943643984232448"
def inputClause4112 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,false),(86,false),(87,false)]
theorem inputList4112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4112 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4112 (by decide) v hb
mask_input "4112|234531609005238064187965440|77992833943643984232450"
def inputClause4113 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,true),(86,false),(87,false)]
theorem inputList4113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4113 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4113 (by decide) v hb
mask_input "4113|232191750199952449822785538|2417851639229258349412352"
def inputClause4114 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,true),(86,false),(87,false)]
theorem inputList4114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4114 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4114 (by decide) v hb
mask_input "4114|232191750199952449822785536|2417851639229258349412354"
def inputClause4115 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,true),(86,false),(87,false)]
theorem inputList4115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4115 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4115 (by decide) v hb
mask_input "4115|232191676412976154984579074|2417925426205553187618816"
def inputClause4116 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,true),(86,false),(87,false)]
theorem inputList4116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4116 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4116 (by decide) v hb
mask_input "4116|232191676412976154984579072|2417925426205553187618818"
def inputClause4117 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,true),(86,false),(87,false)]
theorem inputList4117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4117 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4117 (by decide) v hb
mask_input "4117|232189389016711015000178690|2420212822470693172019200"
def inputClause4118 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,true),(86,false),(87,false)]
theorem inputList4118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4118 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4118 (by decide) v hb
mask_input "4118|232189389016711015000178688|2420212822470693172019202"
def inputClause4119 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,true),(86,false),(87,false)]
theorem inputList4119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4119 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4119 (by decide) v hb
mask_input "4119|232189315229734720161972226|2420286609446988010225664"
def inputClause4120 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,true),(86,false),(87,false)]
theorem inputList4120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4120 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4120 (by decide) v hb
mask_input "4120|232189315229734720161972224|2420286609446988010225666"
def inputClause4121 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,true),(86,false),(87,false)]
theorem inputList4121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4121 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4121 (by decide) v hb
mask_input "4121|232116192336226535499366402|2493409502955172672831488"
def inputClause4122 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,true),(86,false),(87,false)]
theorem inputList4122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4122 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4122 (by decide) v hb
mask_input "4122|232116192336226535499366400|2493409502955172672831490"
def inputClause4124 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(81,true),(86,false),(87,false)]
theorem inputList4124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4124 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4124 (by decide) v hb
mask_input "4124|232116118549250240661159936|2493483289931467511037954"
def inputClause4125 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,true),(86,false),(87,false)]
theorem inputList4125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4125 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4125 (by decide) v hb
mask_input "4125|232113831152985100676759554|2495770686196607495438336"
def inputClause4126 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,true),(86,false),(87,false)]
theorem inputList4126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4126 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4126 (by decide) v hb
mask_input "4126|232113831152985100676759552|2495770686196607495438338"
def inputClause4127 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,true),(86,false),(87,false)]
theorem inputList4127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4127 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4127 (by decide) v hb
mask_input "4127|232113757366008805838553090|2495844473172902333644800"
def inputClause4128 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,true),(86,false),(87,false)]
theorem inputList4128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4128 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4128 (by decide) v hb
mask_input "4128|232113757366008805838553088|2495844473172902333644802"
def inputClause4129 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,false),(86,true),(87,false)]
theorem inputList4129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4129 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4129 (by decide) v hb
mask_input "4129|157238349383845440991002626|77371252455336267181195264"
def inputClause4130 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,false),(86,true),(87,false)]
theorem inputList4130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4130 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4130 (by decide) v hb
mask_input "4130|157238349383845440991002624|77371252455336267181195266"
def inputClause4131 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,false),(86,true),(87,false)]
theorem inputList4131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4131 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4131 (by decide) v hb
mask_input "4131|157238275596869146152796162|77371326242312562019401728"
def inputClause4132 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,false),(81,false),(86,true),(87,false)]
theorem inputList4132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4132 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4132 (by decide) v hb
mask_input "4132|157238275596869146152796160|77371326242312562019401730"
def inputClause4133 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,false),(81,false),(86,true),(87,false)]
theorem inputList4133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4133 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4133 (by decide) v hb
mask_input "4133|157235988200604006168395778|77373613638577702003802112"
def inputClause4134 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,false),(81,false),(86,true),(87,false)]
theorem inputList4134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4134 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4134 (by decide) v hb
mask_input "4134|157235988200604006168395776|77373613638577702003802114"
def inputClause4135 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,false),(81,false),(86,true),(87,false)]
theorem inputList4135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4135 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4135 (by decide) v hb
mask_input "4135|157235914413627711330189314|77373687425553996842008576"
def inputClause4136 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,false),(81,false),(86,true),(87,false)]
theorem inputList4136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4136 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4136 (by decide) v hb
mask_input "4136|157235914413627711330189312|77373687425553996842008578"
def inputClause4137 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,true),(81,false),(86,true),(87,false)]
theorem inputList4137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4137 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4137 (by decide) v hb
mask_input "4137|157162791520119526667583490|77446810319062181504614400"
def inputClause4138 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,true),(81,false),(86,true),(87,false)]
theorem inputList4138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4138 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4138 (by decide) v hb
mask_input "4138|157162791520119526667583488|77446810319062181504614402"
def inputClause4139 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,true),(81,false),(86,true),(87,false)]
theorem inputList4139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4139 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4139 (by decide) v hb
mask_input "4139|157162717733143231829377026|77446884106038476342820864"
def inputClause4140 : CNF.NClause := [(32,false),(1,true),(66,true),(71,false),(76,true),(81,false),(86,true),(87,false)]
theorem inputList4140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4140 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4140 (by decide) v hb
mask_input "4140|157162717733143231829377024|77446884106038476342820866"
def inputClause4141 : CNF.NClause := [(32,false),(1,false),(66,false),(71,true),(76,true),(81,false),(86,true),(87,false)]
theorem inputList4141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4141 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4141 (by decide) v hb
mask_input "4141|157160430336878091844976642|77449171502303616327221248"
def inputClause4142 : CNF.NClause := [(32,false),(1,true),(66,false),(71,true),(76,true),(81,false),(86,true),(87,false)]
theorem inputList4142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4142 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4142 (by decide) v hb
mask_input "4142|157160430336878091844976640|77449171502303616327221250"
def inputClause4143 : CNF.NClause := [(32,false),(1,false),(66,true),(71,true),(76,true),(81,false),(86,true),(87,false)]
theorem inputList4143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4143 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4143 (by decide) v hb
mask_input "4143|157160356549901797006770178|77449245289279911165427712"
def inputClause4144 : CNF.NClause := [(32,false),(1,true),(66,true),(71,true),(76,true),(81,false),(86,true),(87,false)]
theorem inputList4144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4144 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4144 (by decide) v hb
mask_input "4144|157160356549901797006770176|77449245289279911165427714"
def inputClause4145 : CNF.NClause := [(32,false),(1,false),(66,false),(71,false),(76,false),(81,true),(86,true),(87,false)]
theorem inputList4145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4145 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4145 (by decide) v hb
mask_input "4145|154820497744616182641590274|79789104094565525530607616"
def inputClause4146 : CNF.NClause := [(32,false),(1,true),(66,false),(71,false),(76,false),(81,true),(86,true),(87,false)]
theorem inputList4146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4146 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4146 (by decide) v hb
mask_input "4146|154820497744616182641590272|79789104094565525530607618"
def inputClause4147 : CNF.NClause := [(32,false),(1,false),(66,true),(71,false),(76,false),(81,true),(86,true),(87,false)]
theorem inputList4147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4147 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 1) (spread_mem 1) inputClause4147 (by decide) v hb
mask_input "4147|154820423957639887803383810|79789177881541820368814080"
end Percolation.MaskChain
