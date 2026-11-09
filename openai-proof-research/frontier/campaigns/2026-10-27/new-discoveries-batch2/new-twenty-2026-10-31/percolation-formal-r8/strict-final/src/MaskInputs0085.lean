import MaskChainBuild
namespace Percolation.MaskChain
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def inputClause4839 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,false),(82,true),(91,true)]
theorem inputList4839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4839 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4839 (by decide) v hb
mask_input "4839|321120920835273313484864|2480717036227816078746583040"
def inputClause4840 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,false),(82,true),(91,true)]
theorem inputList4840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4840 (by decide) v hb
mask_input "4840|321120920835273313484800|2480717036227816078746583104"
def inputClause4841 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,false),(82,true),(91,true)]
theorem inputList4841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4841 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4841 (by decide) v hb
mask_input "4841|303485833500806982139968|2480734671315150545077927936"
def inputClause4842 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,false),(82,true),(91,true)]
theorem inputList4842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4842 (by decide) v hb
mask_input "4842|303485833500806982139904|2480734671315150545077928000"
def inputClause4843 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,false),(82,true),(91,true)]
theorem inputList4843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4843 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4843 (by decide) v hb
mask_input "4843|303412046524512143933504|2480734745102126839916134400"
def inputClause4844 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,false),(82,true),(91,true)]
theorem inputList4844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4844 (by decide) v hb
mask_input "4844|303412046524512143933440|2480734745102126839916134464"
def inputClause4845 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,false),(82,true),(91,true)]
theorem inputList4845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4845 (by decide) v hb
mask_input "4845|302305241880089570836544|2480735851906771262489231360"
def inputClause4846 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,false),(82,true),(91,true)]
theorem inputList4846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4846 (by decide) v hb
mask_input "4846|302305241880089570836480|2480735851906771262489231424"
def inputClause4847 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,true),(78,false),(82,true),(91,true)]
theorem inputList4847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4847 (by decide) v hb
mask_input "4847|302231454903794732630080|2480735925693747557327437824"
def inputClause4848 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,false),(82,true),(91,true)]
theorem inputList4848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4848 (by decide) v hb
mask_input "4848|302231454903794732630016|2480735925693747557327437888"
def inputClause4849 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,false),(78,true),(82,true),(91,true)]
theorem inputList4849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4849 (by decide) v hb
mask_input "4849|20143844528628269318208|2481018013304122723790749696"
def inputClause4850 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,false),(78,true),(82,true),(91,true)]
theorem inputList4850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4850 (by decide) v hb
mask_input "4850|20143844528628269318144|2481018013304122723790749760"
def inputClause4851 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,false),(78,true),(82,true),(91,true)]
theorem inputList4851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4851 (by decide) v hb
mask_input "4851|20070057552333431111744|2481018087091099018628956160"
def inputClause4852 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,false),(78,true),(82,true),(91,true)]
theorem inputList4852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4852 (by decide) v hb
mask_input "4852|20070057552333431111680|2481018087091099018628956224"
def inputClause4853 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,false),(78,true),(82,true),(91,true)]
theorem inputList4853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4853 (by decide) v hb
mask_input "4853|18963252907910858014784|2481019193895743441202053120"
def inputClause4854 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,false),(78,true),(82,true),(91,true)]
theorem inputList4854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4854 (by decide) v hb
mask_input "4854|18963252907910858014720|2481019193895743441202053184"
def inputClause4855 : CNF.NClause := [(37,false),(6,false),(66,true),(70,true),(74,false),(78,true),(82,true),(91,true)]
theorem inputList4855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4855 (by decide) v hb
mask_input "4855|18889465931616019808320|2481019267682719736040259584"
def inputClause4856 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,false),(78,true),(82,true),(91,true)]
theorem inputList4856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4856 (by decide) v hb
mask_input "4856|18889465931616019808256|2481019267682719736040259648"
def inputClause4857 : CNF.NClause := [(37,false),(6,false),(66,false),(70,false),(74,true),(78,true),(82,true),(91,true)]
theorem inputList4857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4857 (by decide) v hb
mask_input "4857|1254378597149688463424|2481036902770054202371604480"
def inputClause4858 : CNF.NClause := [(37,false),(6,true),(66,false),(70,false),(74,true),(78,true),(82,true),(91,true)]
theorem inputList4858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4858 (by decide) v hb
mask_input "4858|1254378597149688463360|2481036902770054202371604544"
def inputClause4859 : CNF.NClause := [(37,false),(6,false),(66,true),(70,false),(74,true),(78,true),(82,true),(91,true)]
theorem inputList4859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4859 (by decide) v hb
mask_input "4859|1180591620854850256960|2481036976557030497209810944"
def inputClause4860 : CNF.NClause := [(37,false),(6,true),(66,true),(70,false),(74,true),(78,true),(82,true),(91,true)]
theorem inputList4860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4860 (by decide) v hb
mask_input "4860|1180591620854850256896|2481036976557030497209811008"
def inputClause4861 : CNF.NClause := [(37,false),(6,false),(66,false),(70,true),(74,true),(78,true),(82,true),(91,true)]
theorem inputList4861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4861 (by decide) v hb
mask_input "4861|73786976432277160000|2481038083361674919782907904"
def inputClause4862 : CNF.NClause := [(37,false),(6,true),(66,false),(70,true),(74,true),(78,true),(82,true),(91,true)]
theorem inputList4862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4862 (by decide) v hb
mask_input "4862|73786976432277159936|2481038083361674919782907968"
def inputClause4864 : CNF.NClause := [(37,false),(6,true),(66,true),(70,true),(74,true),(78,true),(82,true),(91,true)]
theorem inputList4864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 6) (spread_mem 6) inputClause4864 (by decide) v hb
mask_input "4864|137438953472|2481038157148651214621114432"
def inputClause4994 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,false),(79,false),(82,false),(90,false)]
theorem inputList4994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4994 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause4994 (by decide) v hb
mask_input "4994|1243456095378765897036464128|256"
def inputClause4995 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,false),(79,false),(82,false),(90,false)]
theorem inputList4995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4995 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause4995 (by decide) v hb
mask_input "4995|1243456058485277749617361152|36893488147419103232"
def inputClause4996 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,false),(79,false),(82,false),(90,false)]
theorem inputList4996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4996 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause4996 (by decide) v hb
mask_input "4996|1243456058485277749617360896|36893488147419103488"
def inputClause4997 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,false),(79,false),(82,false),(90,false)]
theorem inputList4997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4997 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause4997 (by decide) v hb
mask_input "4997|1243455800230860717683638528|295147905179352825856"
def inputClause4998 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,false),(79,false),(82,false),(90,false)]
theorem inputList4998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4998 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause4998 (by decide) v hb
mask_input "4998|1243455800230860717683638272|295147905179352826112"
def inputClause4999 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,false),(79,false),(82,false),(90,false)]
theorem inputList4999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause4999 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause4999 (by decide) v hb
mask_input "4999|1243455763337372570264535296|332041393326771929088"
def inputClause5000 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,false),(79,false),(82,false),(90,false)]
theorem inputList5000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5000 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5000 (by decide) v hb
mask_input "5000|1243455763337372570264535040|332041393326771929344"
def inputClause5001 : CNF.NClause := [(39,false),(8,false),(65,false),(68,false),(76,true),(79,false),(82,false),(90,false)]
theorem inputList5001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5001 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5001 (by decide) v hb
mask_input "5001|1243380537515039982713045248|75557863725914323419136"
def inputClause5002 : CNF.NClause := [(39,false),(8,true),(65,false),(68,false),(76,true),(79,false),(82,false),(90,false)]
theorem inputList5002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5002 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5002 (by decide) v hb
mask_input "5002|1243380537515039982713044992|75557863725914323419392"
def inputClause5003 : CNF.NClause := [(39,false),(8,false),(65,true),(68,false),(76,true),(79,false),(82,false),(90,false)]
theorem inputList5003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5003 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5003 (by decide) v hb
mask_input "5003|1243380500621551835293942016|75594757214061742522368"
def inputClause5004 : CNF.NClause := [(39,false),(8,true),(65,true),(68,false),(76,true),(79,false),(82,false),(90,false)]
theorem inputList5004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5004 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5004 (by decide) v hb
mask_input "5004|1243380500621551835293941760|75594757214061742522624"
def inputClause5005 : CNF.NClause := [(39,false),(8,false),(65,false),(68,true),(76,true),(79,false),(82,false),(90,false)]
theorem inputList5005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5005 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5005 (by decide) v hb
mask_input "5005|1243380242367134803360219392|75853011631093676244992"
def inputClause5006 : CNF.NClause := [(39,false),(8,true),(65,false),(68,true),(76,true),(79,false),(82,false),(90,false)]
theorem inputList5006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5006 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5006 (by decide) v hb
mask_input "5006|1243380242367134803360219136|75853011631093676245248"
def inputClause5007 : CNF.NClause := [(39,false),(8,false),(65,true),(68,true),(76,true),(79,false),(82,false),(90,false)]
theorem inputList5007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5007 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5007 (by decide) v hb
mask_input "5007|1243380205473646655941116160|75889905119241095348224"
def inputClause5008 : CNF.NClause := [(39,false),(8,true),(65,true),(68,true),(76,true),(79,false),(82,false),(90,false)]
theorem inputList5008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) inputClause5008 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 8) (spread_mem 8) inputClause5008 (by decide) v hb
mask_input "5008|1243380205473646655941115904|75889905119241095348480"
end Percolation.MaskChain
