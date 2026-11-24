import YM.Avian.Caps
/-! All row receipts after choice Q corrections.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Jewels
open Function Lattice RG Source Wilson Filter Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Intag MassFields
open Lining Lining.Temper Tawny Cast Patria.Rolls Patria.Rolls.Attain Seals Pane BendR UV.Free KeysP Clifford
variable {S:Scheme}{R:Side}{i N:ℕ}(A:Run S N R 6)(T:SourceRead.TaperHol)(sym:RawSym)(B:Bore 8)(hT:Rubric sym B)(F:PatchMix 8)(hf:OrderMix A T sym B (i:=0) F)
variable (x:ℂ)(Q:RawTensor x 8)
set_option quotPrecheck false
local notation "M★"=> S.side R 0
local notation "W'"=> A.density 0
local notation "Yχ"=> vine A B F x Q
variable (hA:A.Actual)(hI:∀ t b i, Lat.Invariant (B t b i))(i j:Axis)(C:Axis→Axis→Label 10)(he:∀ i j, Tally T 0 (C i j) (A.density 0) (trolley A (vine A B F x Q i j) (shelV j) 0 0))
local notation "cR"=>path A B F x Q
variable (D:RawVec 10)(hD:∀ j: Axis,D.val j=∑ i:Axis,C i j)
variable (P:BudgetPoint)(n m:ℕ)(t a:ℝ)(hN:10 ≤ P.order)(hm:6 ≤ n)(hC:2 < m)(ht:0<t)(hQ:∀ i j:Axis, Tutor 0 P (Canvas.foil (A.density 0) ((path A B F x Q i j 0))) t n m a)
variable (hh:3 ≤ P.power)
noncomputable abbrev pointG:=Gpick
lemma ask (j:Fin 3):  ∀ (P:BudgetPoint), 10 ≤ P.order → 3 ≤ P.power→ ∃ K:ℝ,0 ≤ K ∧ ∀ {S:Scheme}{R:Side}{N:ℕ}(A:Run S N R 6)(sym:RawSym)(B:Bore 8)(hT:Rubric sym B)(F:PatchMix 8)(hf:OrderMix A T sym B (i:=0) F)(x:ℂ)(Q:RawTensor x 8)(hA:A.Actual)(hI:∀ t b i, Lat.Invariant (B t b i))(C:Axis→Axis→Label 10)(he:∀ i j, Tally T 0 (C i j) (A.density 0) (trolley A (vine A B F x Q i j) (shelV j) 0 0))(D:RawVec 10)(hD:∀ j: Axis,D.val j=∑ i:Axis,C i j)(n m:ℕ)(t a:ℝ)(hQ:∀ i j:Axis, Tutor 0 P (Canvas.foil (A.density 0) ((path A B F x Q i j 0))) t n m a),
        ‖gaugeQ D j-gaugeA x Q j‖≤4*(((S.side R 0).val:ℝ)⁻¹*(K*a)):=by
    intro P hn hP; let X:= veil Gpick j; let Y:=torchK Gpick j
    choose K hK ht using fun a:Axis=> surfaceT P Gpick X Y T a hP hn (posts j).1 (posts j).2 ruby_pick.choose_spec
    let C':= ∑ i: Axis,K i; refine ⟨C',sum_nonneg fun i _=> hK i,fun {S R N} A sym B hT F hf x Q hA hI C he D hD n m t a hQ=>?_⟩
    let S₁:= S.side R 0; let D':=(0:Axis); let A'(k:Axis):=capote 10 (leanY X Y) (C k D'); let B'(k:Axis):= pan X Y k (Q.val (k,D'))
    have hG (k:Axis): ‖A' k-B' k‖ ≤ (S₁.val:ℝ)⁻¹ * (C'*a):=by
         let G:= A.density 0; let z:= path A B F x Q k D' 0; have h':= hQ k D'; have hw:Tally T 0 (C k D') G (stunt k z):=by rw[←vert1 A T sym B hT F hf x Q hA]; exact he k _
         have ha:0 ≤ a:= (norm_nonneg _).trans (h'.large [] (Nat.zero_le _) (fun _ h=>by simp at h)); have hm(p:Cover): march p G= G:= by unfold G; rw [pier A hA (Nat.zero_le _)]; exact Depth.first _ _ (Nat.zero_le _) _
         refine (ht k S₁ z G _ _ _ _ _ _ h' (readS A T sym B hT F hf x Q hA k D') (signs A B F x Q k _ hI 0) (lived A hA) hm hw).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (single_le_sum (fun i _=>hK i) (mem_univ k)) ha) (by positivity)) -- signs parameter order
    change ‖capote 10 _ (D.val D')-_‖ ≤ _; rw [hD,map_sum,Seals.gaugeV]; exact dueT A' B' _ hG
include hQ he hN hm hA hh hD hI hC ht hT hf
variable (b:Flavor 6)(v u:Fiber)
local notation "Bq"=> (4:ℝ)*(4*2^P.power*(a/t^2))
local notation "Kx"=> Canvas.foil W' (castG A B F x Q (0:Axis))
lemma lookV (K:ℝ) (hK:∀ c:Side,∀ (F P':Density c 6)(n:ℕ)(D:ℝ)(Z:Label 10), Allow P Gpick (Canvas.foil P' F) n D→SungP (Canvas.foil P' F)→Tally T 0 Z P' F→ 10 ≤ n →∀ p i j, ‖river2 0 1 p i j Gpick (Canvas.foil P' F)-awake2 0 1 p i j Gpick Z‖≤ (c.val:ℝ)⁻¹*K*D): ‖lookQ D b (v,u)‖ ≤ ((S.side R 0).val:ℝ)⁻¹*K*Bq∧ ‖lookB D b (v,u)‖≤ costQ 2*tick (S.side R 0)*Bq:=by
    have H:=totals A T sym B hT F hf x Q hA 0 C he D hD; let J:=castG A B F x Q (0:Axis); obtain ⟨hL,hU,hF,hG⟩:= nobledP A T sym B hT F hf x Q hA hI C he D hD P n m t a hN hm hC ht hQ v u (0:Axis) b 0 1; have hp:=hK (S.side R 0) J W' _ Bq (D.val (0:Axis)) hL hU H hN b v u; change river2 _ _ _ _ _ _ _=0 at hF; rw [hF,zero_sub,norm_neg] at hp
    have h:= (nobledP A T sym B hT F hf x Q hA hI C he D hD P n m t a hN hm hC ht hQ v u (0:Axis) b 1 0).2.2.2; have hv:= bracken P Gpick 1 T v u b W' J (D.val (0:Axis)) H hL; rw[show river1 1 b v u (Canvas.foil W' J)=0 from h,zero_sub,norm_neg] at hv -- args order
    exact ⟨hp,hv⟩
end YM.Massive.Patria.Gall.Jewels
#print axioms YM.Massive.Patria.Gall.Jewels.lookV
