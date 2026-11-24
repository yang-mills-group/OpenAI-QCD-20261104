import YM.QCD.Loom.Issue
import YM.Mills.Glow
/-! # expenses transferred for Camp stamps no lost seed count -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β b τ μ W C:ℝ} {F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W} {R : BudgetPoint}
variable {H:Cash W τ μ L Q o C T (trimP T R δ β b)}{ι D E K:Type}{N:ℕ}
local notation "Ξ" => Fj D E K
variable (H :Cash W τ μ L Q o C T (trimP T R δ β b)) (Y:Send S.ratio N D)(p:Rise f N E K)(X:Fj D E K→Support c)
variable [Fintype D][Countable E][Countable K]
local notation "A" => Wound X
local notation "t"=>R.threshold
local notation "PI"=> trimP T R δ β b
local notation "Y'"=> (deckHue H Y p X)
variable {m : D→ℝ} {q : E→ℝ}{e : K→ℝ} {w h v z ζ γ κ u d r:ℝ}{i n:ℕ}
namespace Mint
local notation "sV"=> lantern L τ
def vipM (q:E→ℝ)(e:K→ℝ)(m:D→ℝ)(w:ℝ)(c:ℝ) (j:Wound X):= c^(spent j.1).card*mintD H Y p X m q e w j
lemma incomeR {cS:ℝ} (H':Peak Y t h v w m)(hm:Cents p q e h t)(hp:p.Wave t)(hY:Ready X n (paidSet Y p m q e w 1 r cS) z γ κ d)(hw:1 ≤ r)(hy:0≤cS)(hd:0<δ)(hv:δ⁻¹ ≤ r)(hs:0≤z):Ac.Hit (Y').ground n (vipM H Y p X q e m w cS) z (γ*(1-d)⁻¹):=by
  intro y; let p' s:=vipM H Y p X q e m w cS s
  have hh:=value_hit Y p H' hm hp hY hs le_rfl hw hy y 0
  have hm0:= budget_pull ((↑):Wound X→Finset Ξ) Subtype.val_injective hh
  simp only [one_mul,pow_zero,mul_one,Nat.zero_le,true_and,and_true] at hm0
  have hx(j:A):0≤ jewel Y p X m q e w j.val := (load_nn ..).trans (pinches Y p H' hm hp 1 j.property)
  refine budget_mono hm0 (fun j=>?_) fun j=> ?_
  · split; exact mul_nonneg (mul_nonneg (pow_nonneg hy _) (mul_nonneg (by positivity) (hx j))) (Real.exp_pos _).le; exact le_rfl
  split
  next hk=>
    rw [if_pos (show y∈Finset.biUnion j.val X from hk)]; change p' j * _ ≤ (_*_*_)*_; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; rw [mul_assoc (cS^(_ :ℕ))]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (inv_pos.mpr hd).le hv _).trans (pow_le_pow_right₀ hw (Finset.card_biUnion_le ..))) (hx j)) (pow_nonneg hy _)
  exact hm0.1 _
variable (ν:ℝ) (qx:E→ℝ) (mx:D→ℝ)(F':D→ℝ)(G':E→ℝ) -- error compensation
lemma upland (j:Wound X)(hd:0<δ)(hq:0≤ q)(he:0≤ e)(hm:0≤ m)(hw:1 ≤ w)(ht:1≤ν)(hf:∀ i,1≤ F' i)(hh:∀ i,1 ≤ G' i) (hD:∀ i,m i * F' i ≤ mx i)(hE:∀ i, (Real.exp (q i)-1)*G' i ≤ Real.exp (qx i)-1) :
   let I:=j.val; let v:=ν^(spent I).card * ((∏ i∈ops I,F' i)*∏ i∈leftE I, G' i); v * mintD H Y p X m q e w j ≤ vipM H Y p X qx e mx w ν j:=by
    intro I v'; unfold v' mintD vipM; rw [mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (zero_le_one.trans ht) _); unfold mintD; rw [mul_left_comm]; unfold jewel; refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    split; swap; · rw [mul_zero]
    rw [mul_left_comm]; refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (zero_le_one.trans hw) _); unfold priceSet
    let p1:= ops I; let p2:= leftE I; let p3:= spent I; let w₀:= ∏ j∈p3,e j; let w₁:= ∏ i∈p2,(Real.exp (q i)-1); let w₂:=∏ i∈p2,(Real.exp (qx i)-1); let Fa:=∏ i∈p1,F' i; let B:=∏ i∈p2,G' i
    have hz : w₁*B ≤ w₂:=by unfold w₁ B; rw [←prod_mul_distrib]; exact prod_le_prod (fun i _=>mul_nonneg (sub_nonneg.mpr (Real.one_le_exp (hq i))) (zero_le_one.trans (hh i))) (fun i _=> hE i)
    have hs : (∏ i∈p1,m i)*Fa ≤ ∏ i∈p1,mx i:=by unfold Fa; rw [← prod_mul_distrib]; exact prod_le_prod (fun i _=> mul_nonneg (hm i) (zero_le_one.trans (hf i))) (fun i _=> hD i)
    have h0: 0 ≤ w₁:= prod_nonneg fun i _=>sub_nonneg.mpr (Real.one_le_exp (hq i)); have h1:0 ≤ w₀:= prod_nonneg fun i _=> he i
    have hv:0 ≤ B:= prod_nonneg fun i _=> zero_le_one.trans (hh i)
    change (Fa*B)*((∏ i∈p1,m i)*(w₁*w₀)) ≤ (∏ i∈p1,mx i)*(w₂*w₀); rw [show (Fa*B)*((∏ i∈p1,m i)*(w₁*w₀))=( (∏ i∈p1,m i)*Fa)* (w₁*B*w₀) from by ring]
    exact mul_le_mul hs (mul_le_mul_of_nonneg_right hz h1) (mul_nonneg (mul_nonneg h0 hv) h1) (prod_nonneg fun i _=> (mul_nonneg (hm i) (zero_le_one.trans (hf i))).trans (hD i))
end Mint
end YM.QCD.Loom
#print axioms YM.QCD.Loom.Mint.incomeR
#print axioms YM.QCD.Loom.Mint.upland
