import YM.QCD.Loom.Hall
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
def lowK (L:Side)(x a:ℝ) := incomingK su L x*Real.exp (-a)
lemma dipK (L:Side)(a:ℝ):∀ᶠ x in atTop,0<lowK L x a∧ Real.exp a*|lowK L x a| ≤ incomingK su L x ∧ (lowK L x a)⁻¹ ≤taxK L x (1/2):=by
   have hg:= show Jets.Touch.Seat L (1/5) (fun x=>a+pra L x^(1/5:ℝ)) from ((Jets.Touch.Seat.numbers a).above (by norm_num)).comb Jets.Touch.Seat.keeps
   filter_upwards [hg.timesL 2 ((1:ℝ)/3) (by norm_num)] with x hx
   let k:= incomingK su L x; let t':= Real.exp (-a); let p:=pra L x; have he:k=Real.exp (-(p^(1/5:ℝ))):=rfl; have hp:0<k:= he.symm ▸ Real.exp_pos _; have hF:0<t':=Real.exp_pos _; have hl : 0< lowK L x a:= mul_pos hp hF
   refine ⟨hl, ?_,?_⟩
   · rw [abs_of_pos hl]; unfold lowK; rw [mul_left_comm,← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
   unfold lowK; rw [mul_inv]; change k⁻¹* t'⁻¹ ≤ _; rw [he,Real.exp_neg, show t'= (Real.exp a)⁻¹ from Real.exp_neg _,inv_inv, inv_inv,← Real.exp_add]; unfold taxK; apply Real.exp_monotone
   have he := (le_abs_self _).trans hx; unfold fan p; linarith

def mintD (_ : Cash W τ μ L Q o C T PI) (Y:Send S.ratio N D)(p:Rise f N E K)(X:Fj D E K→Support c)(m : D→ℝ)(q:E→ℝ)(e:K→ℝ)(w:ℝ) (i:Wound X): ℝ := (δ⁻¹ ^ budget p i.1) * jewel Y p X m q e w i.1
lemma shiner (H' : Peak Y t h v w m) (hm : Cents p q e h t)(hp:p.Wave t)(hz:0<δ) (x: Wound X→Site c)(hA:0≤u): Fleet.Theft (Y') F x (mintD H Y p X m q e w) v u ∅ i n:=by
    let M:=mintD H Y p X m q e w; have hx j :0 ≤ M j:=by have hv:= (load_nn ..).trans (pinches Y p H' hm hp (1:Grid f) j.property); exact mul_nonneg (by positivity) hv -- type
    have hk j (X':Coat T F) z: ‖token _ _ v ((Y').coming j X' z)‖ ≤ M j:=by
       let Y'' := deckHue H Y p X; let a:=j.val; let p' := X'.input (X'.liftA β z); let y:=hue Y p t a p'
       apply (Y''.riseTiny X' z _ j v).trans; change ‖token c N v (δ⁻¹ ^ budget p a • y)‖ ≤ M j
       rw [map_smul,norm_smul,Real.norm_of_nonneg (by positivity : 0≤ δ⁻¹ ^ budget p a)]; exact mul_le_mul_of_nonneg_left (pinches Y p H' hm hp p' j.property) (by positivity)
    refine ⟨hA,hx,(by simp),fun j X _ _ _ z h=> False.elim ((not_lt.mpr (hk j X z)) h), fun j X _ _ _ z=> (hk j X z).trans (le_mul_of_one_le_left (hx j) (Real.one_le_exp hA))⟩
lemma revenueX (H' : Peak Y t h v w m) (hm:Cents p q e h t) (hp:p.Wave t) (hY: Ready X n (paidSet Y p m q e w ζ r 1) z γ κ d) (hb:1≤ζ)(hw:1≤r)(hd:0<δ)(hv:δ⁻¹ ≤r)(hs:0≤z):Ac.Hit ((Y').ground) n (mintD H Y p X m q e w) z (ζ⁻¹*(γ *(1-d)⁻¹)):=by
  intro y
  let p' s :=mintD H Y p X m q e w s
  have hH:=value_hit Y p H' hm hp hY hs hb hw zero_le_one y 0
  have he := zero_lt_one.trans_le hb; have hp := budget_pull ((↑): Wound X→Finset Ξ) Subtype.val_injective hH
  simp only [pow_zero,one_pow,mul_one,Nat.zero_le,true_and,and_true] at hp
  have hx (j:A):0≤ jewel Y p X m q e w j.val:= (load_nn ..).trans (pinches Y p H' hm ‹p.Wave R.threshold› 1 j.property)
  refine budget_mono (budget_scale (inv_pos.mpr he).le hp) (fun j=> ?_) fun j => ?_
  · split; exact mul_nonneg (mul_nonneg (by positivity) (hx j)) (Real.exp_pos _).le; exact le_rfl
  split
  next hk=>
    rw [if_pos (show y∈Finset.biUnion j.val X from hk)]; change p' j * _≤ _ * _; unfold p' mintD; --edit
    rw [← mul_assoc,←mul_assoc,←mul_assoc,inv_mul_cancel₀ he.ne',one_mul]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (inv_pos.mpr hd).le hv _).trans (pow_le_pow_right₀ hw (Finset.card_biUnion_le ..))) (hx j)
  exact (budget_scale (inv_pos.mpr he).le hp).1 _
end YM.QCD.Loom
