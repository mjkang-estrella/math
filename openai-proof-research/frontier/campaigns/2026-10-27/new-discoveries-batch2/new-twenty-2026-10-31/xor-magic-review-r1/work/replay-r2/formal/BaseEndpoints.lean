import Base16Open5
import Base16Open7
import Base16Open9
import Base16Open11
import Base16Closed4
import Base16Closed6
import Base16Closed8
import Base16Closed10
import Base32Open5
import Base32Open7
import Base32Open9
import Base32Open11
import Base32Open13
import Base32Open15
import Base32Open17
import Base32Open19
import Base32Open21
import Base32Open23
import Base32Open25
import Base32Open27
import Base32Closed4
import Base32Closed6
import Base32Closed8
import Base32Closed10
import Base32Closed12
import Base32Closed14
import Base32Closed16
import Base32Closed18
import Base32Closed20
import Base32Closed22
import Base32Closed24
import Base32Closed26
namespace XorMagic
theorem corrected_at_4 : CorrectedAt 4 := by
  constructor
  · intro d hd hlo hhi
    rcases hd with ⟨k, hk⟩
    norm_num at hhi
    interval_cases d <;> first
      | exact Base16Open5.exists_literal
      | exact Base16Open7.exists_literal
      | exact Base16Open9.exists_literal
      | exact Base16Open11.exists_literal
      | omega
  · intro d hd hlo hhi
    rcases hd with ⟨k, hk⟩
    norm_num at hhi
    interval_cases d <;> first
      | exact Base16Closed4.exists_literal
      | exact Base16Closed6.exists_literal
      | exact Base16Closed8.exists_literal
      | exact Base16Closed10.exists_literal
      | omega
theorem corrected_at_5 : CorrectedAt 5 := by
  constructor
  · intro d hd hlo hhi
    rcases hd with ⟨k, hk⟩
    norm_num at hhi
    interval_cases d <;> first
      | exact Base32Open5.exists_literal
      | exact Base32Open7.exists_literal
      | exact Base32Open9.exists_literal
      | exact Base32Open11.exists_literal
      | exact Base32Open13.exists_literal
      | exact Base32Open15.exists_literal
      | exact Base32Open17.exists_literal
      | exact Base32Open19.exists_literal
      | exact Base32Open21.exists_literal
      | exact Base32Open23.exists_literal
      | exact Base32Open25.exists_literal
      | exact Base32Open27.exists_literal
      | omega
  · intro d hd hlo hhi
    rcases hd with ⟨k, hk⟩
    norm_num at hhi
    interval_cases d <;> first
      | exact Base32Closed4.exists_literal
      | exact Base32Closed6.exists_literal
      | exact Base32Closed8.exists_literal
      | exact Base32Closed10.exists_literal
      | exact Base32Closed12.exists_literal
      | exact Base32Closed14.exists_literal
      | exact Base32Closed16.exists_literal
      | exact Base32Closed18.exists_literal
      | exact Base32Closed20.exists_literal
      | exact Base32Closed22.exists_literal
      | exact Base32Closed24.exists_literal
      | exact Base32Closed26.exists_literal
      | omega
end XorMagic
