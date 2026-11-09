import Query
import Reduction
import Mathlib.Tactic.SplitIfs
set_option autoImplicit false
set_option warningAsError true
namespace Assembly
open Classical
theorem clip_ite (H : ℕ) (z : ℤ) : FloorSums.clip H z = (if z ≤ 0 then 0 else if z ≥ (H : ℤ) then (H : ℤ) else z) := by
  unfold FloorSums.clip
  simp only [max_def, min_def]
  split_ifs <;> omega
theorem clip_5426 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e5426 v = FloorSums.clip H (e532 v) := by
  unfold e5426 e745 e534 e533 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_5427 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e5427 v = FloorSums.clip H (e535 v) := by
  unfold e5427 e766 e537 e536 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_5428 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e5428 v = FloorSums.clip H (e538 v) := by
  unfold e5428 e787 e540 e539 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_5429 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e5429 v = FloorSums.clip H (e541 v) := by
  unfold e5429 e808 e543 e542 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8763 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8763 v = FloorSums.clip H (e546 v) := by
  unfold e8763 e547 e5430 e548 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8764 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8764 v = FloorSums.clip H (e549 v) := by
  unfold e8764 e550 e5431 e551 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8765 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8765 v = FloorSums.clip H (e552 v) := by
  unfold e8765 e553 e5432 e554 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8766 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8766 v = FloorSums.clip H (e555 v) := by
  unfold e8766 e556 e5433 e557 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8768 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8768 v = FloorSums.clip H (e560 v) := by
  unfold e8768 e561 e5434 e562 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8769 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8769 v = FloorSums.clip H (e563 v) := by
  unfold e8769 e564 e5435 e565 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8770 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8770 v = FloorSums.clip H (e566 v) := by
  unfold e8770 e567 e5436 e568 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8771 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8771 v = FloorSums.clip H (e569 v) := by
  unfold e8771 e570 e5437 e571 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8773 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8773 v = FloorSums.clip H (e573 v) := by
  unfold e8773 e574 e5438 e575 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8774 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8774 v = FloorSums.clip H (e576 v) := by
  unfold e8774 e577 e5439 e578 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8775 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8775 v = FloorSums.clip H (e579 v) := by
  unfold e8775 e580 e5440 e581 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8776 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8776 v = FloorSums.clip H (e582 v) := by
  unfold e8776 e583 e5441 e584 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8778 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8778 v = FloorSums.clip H (e587 v) := by
  unfold e8778 e588 e5442 e589 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8779 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8779 v = FloorSums.clip H (e590 v) := by
  unfold e8779 e591 e5443 e592 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8780 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8780 v = FloorSums.clip H (e593 v) := by
  unfold e8780 e594 e5444 e595 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8781 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8781 v = FloorSums.clip H (e596 v) := by
  unfold e8781 e597 e5445 e598 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8783 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8783 v = FloorSums.clip H (e600 v) := by
  unfold e8783 e601 e5446 e602 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8784 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8784 v = FloorSums.clip H (e603 v) := by
  unfold e8784 e604 e5447 e605 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8785 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8785 v = FloorSums.clip H (e606 v) := by
  unfold e8785 e607 e5448 e608 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8786 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8786 v = FloorSums.clip H (e609 v) := by
  unfold e8786 e610 e5449 e611 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8788 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8788 v = FloorSums.clip H (e613 v) := by
  unfold e8788 e614 e5450 e615 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8789 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8789 v = FloorSums.clip H (e616 v) := by
  unfold e8789 e617 e5451 e618 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8790 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8790 v = FloorSums.clip H (e619 v) := by
  unfold e8790 e620 e5452 e621 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8791 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8791 v = FloorSums.clip H (e622 v) := by
  unfold e8791 e623 e5453 e624 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8793 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8793 v = FloorSums.clip H (e626 v) := by
  unfold e8793 e627 e5454 e628 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8794 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8794 v = FloorSums.clip H (e629 v) := by
  unfold e8794 e630 e5455 e631 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8795 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8795 v = FloorSums.clip H (e632 v) := by
  unfold e8795 e633 e5456 e634 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8796 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8796 v = FloorSums.clip H (e635 v) := by
  unfold e8796 e636 e5457 e637 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8798 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8798 v = FloorSums.clip H (e640 v) := by
  unfold e8798 e641 e5458 e642 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8799 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8799 v = FloorSums.clip H (e643 v) := by
  unfold e8799 e644 e5459 e645 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8800 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8800 v = FloorSums.clip H (e646 v) := by
  unfold e8800 e647 e5460 e648 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8801 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8801 v = FloorSums.clip H (e649 v) := by
  unfold e8801 e650 e5461 e651 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8803 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8803 v = FloorSums.clip H (e653 v) := by
  unfold e8803 e654 e5462 e655 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8804 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8804 v = FloorSums.clip H (e656 v) := by
  unfold e8804 e657 e5463 e658 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8805 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8805 v = FloorSums.clip H (e659 v) := by
  unfold e8805 e660 e5464 e661 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8806 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8806 v = FloorSums.clip H (e662 v) := by
  unfold e8806 e663 e5465 e664 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8808 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8808 v = FloorSums.clip H (e666 v) := by
  unfold e8808 e667 e5466 e668 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8809 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8809 v = FloorSums.clip H (e669 v) := by
  unfold e8809 e670 e5467 e671 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8810 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8810 v = FloorSums.clip H (e672 v) := by
  unfold e8810 e673 e5468 e674 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8811 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8811 v = FloorSums.clip H (e675 v) := by
  unfold e8811 e676 e5469 e677 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8813 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8813 v = FloorSums.clip H (e679 v) := by
  unfold e8813 e680 e5470 e681 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8814 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8814 v = FloorSums.clip H (e682 v) := by
  unfold e8814 e683 e5471 e684 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8815 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8815 v = FloorSums.clip H (e685 v) := by
  unfold e8815 e686 e5472 e687 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8816 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8816 v = FloorSums.clip H (e688 v) := by
  unfold e8816 e689 e5473 e690 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8818 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8818 v = FloorSums.clip H (e692 v) := by
  unfold e8818 e693 e5474 e694 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8819 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8819 v = FloorSums.clip H (e695 v) := by
  unfold e8819 e696 e5475 e697 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8820 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8820 v = FloorSums.clip H (e698 v) := by
  unfold e8820 e699 e5476 e700 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8821 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8821 v = FloorSums.clip H (e701 v) := by
  unfold e8821 e702 e5477 e703 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8823 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8823 v = FloorSums.clip H (e705 v) := by
  unfold e8823 e706 e5478 e707 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8824 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8824 v = FloorSums.clip H (e708 v) := by
  unfold e8824 e709 e5479 e710 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8825 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8825 v = FloorSums.clip H (e711 v) := by
  unfold e8825 e712 e5480 e713 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8826 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8826 v = FloorSums.clip H (e714 v) := by
  unfold e8826 e715 e5481 e716 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8828 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8828 v = FloorSums.clip H (e718 v) := by
  unfold e8828 e719 e5482 e720 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8829 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8829 v = FloorSums.clip H (e721 v) := by
  unfold e8829 e722 e5483 e723 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8830 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8830 v = FloorSums.clip H (e724 v) := by
  unfold e8830 e725 e5484 e726 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_8831 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e8831 v = FloorSums.clip H (e727 v) := by
  unfold e8831 e728 e5485 e729 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_5489 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e5489 v = FloorSums.clip H (e731 v) := by
  unfold e5489 e5486 e5488 e5487 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_5493 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e5493 v = FloorSums.clip H (e732 v) := by
  unfold e5493 e5490 e5492 e5491 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_5497 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e5497 v = FloorSums.clip H (e733 v) := by
  unfold e5497 e5494 e5496 e5495 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
theorem clip_5501 (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e5501 v = FloorSums.clip H (e734 v) := by
  unfold e5501 e5498 e5500 e5499 e12 e17
  rw [hH]
  simp only [clip_ite]
  split_ifs <;> rfl
end Assembly
