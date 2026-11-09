import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4712 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,false),(86,true),(92,true)]
theorem inputList4712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4712 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4712 (by decide) v hb
mask_input "4712|58028439341502269105373184|5043638519432232916874166304"
def inputClause4713 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,false),(86,true),(92,true)]
theorem inputList4713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4713 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4713 (by decide) v hb
mask_input "4713|53192736063043752406548512|5048474222710691433572990976"
def inputClause4714 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,false),(86,true),(92,true)]
theorem inputList4714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4714 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4714 (by decide) v hb
mask_input "4714|53192736063043752406548480|5048474222710691433572991008"
def inputClause4715 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,false),(86,true),(92,true)]
theorem inputList4715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4715 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4715 (by decide) v hb
mask_input "4715|48357032784585235707723808|5053309925989149950271815680"
def inputClause4716 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,false),(86,true),(92,true)]
theorem inputList4716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4716 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4716 (by decide) v hb
mask_input "4716|48357032784585235707723776|5053309925989149950271815712"
def inputClause4717 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,true),(85,false),(86,true),(92,true)]
theorem inputList4717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4717 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4717 (by decide) v hb
mask_input "4717|43521329506126719008899104|5058145629267608466970640384"
def inputClause4718 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,false),(86,true),(92,true)]
theorem inputList4718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4718 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4718 (by decide) v hb
mask_input "4718|43521329506126719008899072|5058145629267608466970640416"
def inputClause4719 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,true),(85,false),(86,true),(92,true)]
theorem inputList4719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4719 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4719 (by decide) v hb
mask_input "4719|38685626227668202310074400|5062981332546066983669465088"
def inputClause4720 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,false),(86,true),(92,true)]
theorem inputList4720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4720 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4720 (by decide) v hb
mask_input "4720|38685626227668202310074368|5062981332546066983669465120"
def inputClause4721 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,false),(85,true),(86,true),(92,true)]
theorem inputList4721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4721 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4721 (by decide) v hb
mask_input "4721|33849922949209685611249696|5067817035824525500368289792"
def inputClause4722 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,false),(85,true),(86,true),(92,true)]
theorem inputList4722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4722 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4722 (by decide) v hb
mask_input "4722|33849922949209685611249664|5067817035824525500368289824"
def inputClause4723 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,false),(85,true),(86,true),(92,true)]
theorem inputList4723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4723 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4723 (by decide) v hb
mask_input "4723|29014219670751168912424992|5072652739102984017067114496"
def inputClause4724 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,false),(85,true),(86,true),(92,true)]
theorem inputList4724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4724 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4724 (by decide) v hb
mask_input "4724|29014219670751168912424960|5072652739102984017067114528"
def inputClause4725 : CNF.NClause := [(36,false),(5,false),(82,false),(83,true),(84,false),(85,true),(86,true),(92,true)]
theorem inputList4725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4725 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4725 (by decide) v hb
mask_input "4725|24178516392292652213600288|5077488442381442533765939200"
def inputClause4726 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,false),(85,true),(86,true),(92,true)]
theorem inputList4726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4726 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4726 (by decide) v hb
mask_input "4726|24178516392292652213600256|5077488442381442533765939232"
def inputClause4727 : CNF.NClause := [(36,false),(5,false),(82,true),(83,true),(84,false),(85,true),(86,true),(92,true)]
theorem inputList4727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4727 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4727 (by decide) v hb
mask_input "4727|19342813113834135514775584|5082324145659901050464763904"
def inputClause4728 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,false),(85,true),(86,true),(92,true)]
theorem inputList4728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4728 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4728 (by decide) v hb
mask_input "4728|19342813113834135514775552|5082324145659901050464763936"
def inputClause4729 : CNF.NClause := [(36,false),(5,false),(82,false),(83,false),(84,true),(85,true),(86,true),(92,true)]
theorem inputList4729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4729 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4729 (by decide) v hb
mask_input "4729|14507109835375618815950880|5087159848938359567163588608"
def inputClause4730 : CNF.NClause := [(36,false),(5,true),(82,false),(83,false),(84,true),(85,true),(86,true),(92,true)]
theorem inputList4730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4730 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4730 (by decide) v hb
mask_input "4730|14507109835375618815950848|5087159848938359567163588640"
def inputClause4731 : CNF.NClause := [(36,false),(5,false),(82,true),(83,false),(84,true),(85,true),(86,true),(92,true)]
theorem inputList4731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4731 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4731 (by decide) v hb
mask_input "4731|9671406556917102117126176|5091995552216818083862413312"
def inputClause4732 : CNF.NClause := [(36,false),(5,true),(82,true),(83,false),(84,true),(85,true),(86,true),(92,true)]
theorem inputList4732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4732 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4732 (by decide) v hb
mask_input "4732|9671406556917102117126144|5091995552216818083862413344"
def inputClause4734 : CNF.NClause := [(36,false),(5,true),(82,false),(83,true),(84,true),(85,true),(86,true),(92,true)]
theorem inputList4734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4734 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4734 (by decide) v hb
mask_input "4734|4835703278458585418301440|5096831255495276600561238048"
def inputClause4736 : CNF.NClause := [(36,false),(5,true),(82,true),(83,true),(84,true),(85,true),(86,true),(92,true)]
theorem inputList4736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4736 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 5) (spread_mem 5) inputClause4736 (by decide) v hb
mask_input "4736|68719476736|5101666958773735117260062752"
def inputClause4738 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,false),(82,false),(91,false)]
theorem inputList4738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4738 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4738 (by decide) v hb
mask_input "4738|2481038157148651352060067840|64"
def inputClause4739 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,false),(82,false),(91,false)]
theorem inputList4739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4739 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4739 (by decide) v hb
mask_input "4739|2481038083361675057221861440|73786976294838206464"
def inputClause4740 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,false),(82,false),(91,false)]
theorem inputList4740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4740 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4740 (by decide) v hb
mask_input "4740|2481038083361675057221861376|73786976294838206528"
def inputClause4741 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,false),(82,false),(91,false)]
theorem inputList4741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4741 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4741 (by decide) v hb
mask_input "4741|2481036976557030634648764480|1180591620717411303424"
def inputClause4742 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,false),(82,false),(91,false)]
theorem inputList4742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4742 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4742 (by decide) v hb
mask_input "4742|2481036976557030634648764416|1180591620717411303488"
def inputClause4743 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,false),(82,false),(91,false)]
theorem inputList4743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4743 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4743 (by decide) v hb
mask_input "4743|2481036902770054339810558016|1254378597012249509888"
def inputClause4744 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,false),(82,false),(91,false)]
theorem inputList4744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4744 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4744 (by decide) v hb
mask_input "4744|2481036902770054339810557952|1254378597012249509952"
def inputClause4745 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,false),(82,false),(91,false)]
theorem inputList4745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4745 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4745 (by decide) v hb
mask_input "4745|2481019267682719873479213120|18889465931478580854784"
def inputClause4746 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,false),(82,false),(91,false)]
theorem inputList4746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4746 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4746 (by decide) v hb
mask_input "4746|2481019267682719873479213056|18889465931478580854848"
def inputClause4747 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,false),(82,false),(91,false)]
theorem inputList4747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4747 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4747 (by decide) v hb
mask_input "4747|2481019193895743578641006656|18963252907773419061248"
def inputClause4748 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,false),(82,false),(91,false)]
theorem inputList4748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4748 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4748 (by decide) v hb
mask_input "4748|2481019193895743578641006592|18963252907773419061312"
def inputClause4749 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,false),(82,false),(91,false)]
theorem inputList4749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4749 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4749 (by decide) v hb
mask_input "4749|2481018087091099156067909696|20070057552195992158208"
def inputClause4750 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,false),(82,false),(91,false)]
theorem inputList4750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4750 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4750 (by decide) v hb
mask_input "4750|2481018087091099156067909632|20070057552195992158272"
def inputClause4751 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,true),(78,false),(82,false),(91,false)]
theorem inputList4751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4751 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4751 (by decide) v hb
mask_input "4751|2481018013304122861229703232|20143844528490830364672"
def inputClause4752 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,false),(82,false),(91,false)]
theorem inputList4752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4752 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4752 (by decide) v hb
mask_input "4752|2481018013304122861229703168|20143844528490830364736"
def inputClause4753 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,true),(82,false),(91,false)]
theorem inputList4753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4753 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4753 (by decide) v hb
mask_input "4753|2480735925693747694766391360|302231454903657293676544"
def inputClause4754 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,true),(82,false),(91,false)]
theorem inputList4754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4754 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4754 (by decide) v hb
mask_input "4754|2480735925693747694766391296|302231454903657293676608"
end Percolation.MaskChain
