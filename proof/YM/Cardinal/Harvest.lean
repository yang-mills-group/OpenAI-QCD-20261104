import YM.Cardinal.Homage
/-! # Accounts with mark exposures, including absent ancestry. This file loops through actual supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {u s t a b θ v A' D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c f L:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
namespace Stamp
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle
variable {I J K E Uv Fv Zt:Type}
variable (H:TaperHol){U:Hol su}(A:Exhibit U)(b:Cover)
variable (x y:Label d) (q:Bool) (Pt:BudgetPoint)
namespace Incidence
local notation "o"=>wrap c b
local notation "GT"=> wealth
variable (P:BudgetPoint) (hk:Pilot H A d m k n j r α β)(ht: Pt.order=m) (hp:Pt.power=k) (Q:Puff c 6 I q)(S:I→Support c)(hQ: Seal 6 (wrap c b) Q)
variable {a₀ a₁ a₂ β₀ ε₀ ε₁ ε₂ ε₃ ε₄ z z₀ ζ F₀ σ χ ζ₁ q₀ p₀:ℝ} (J₀:Jars d → I) (J₁:E→I) (hi:Injective (Sum.elim J₀ J₁)) (R : I→ Prop) (s : E→Support f) (l:E→ℝ)
-- off all EXCEPT R inside J_*. Founder.NonPrimary. Conn.
def exempt : I→ Prop:= fun i=> ¬ (R i ∧ i∈Set.range (Sum.elim J₀ J₁))
local notation "G"=> exempt J₀ J₁ R
local notation "O"=>f -- remove
variable (hA:∀ i, wrap c b∈ S i)(hL:0≤l)
local notation "b₀"=>fun i=>coverNumber Pt.B (S i)
local notation "b₁"=>fun i=>coverNumber P.B (s i)
variable (v₀:E→ℝ)
-- Coin estimates already from prebit with α₁ input reserve. At all traces.More points.U.Hopes.
local notation "Za"=> fun i=> z₀^(d+1)*C*Real.exp (a₂*b₁ i-u* b₀ (J₁ i))*l i
variable (hG:∀ i:Jars d,R (J₀ i))
-- caps step.Remainder.
variable (hD:∀ i:E, R (J₁ i)→ Flame (Q.fill (J₁ i)) Pt (S (J₁ i)) (wrap c b) v n j (z₀^(d+1)*C*Real.exp (a₂ * coverNumber P.B (s i)-u*coverNumber Pt.B (S (J₁ i)))*l i))
-- off other.E root all.Ty.Line.Unity * actual h.
variable {U₁ U₂ B'ₘ:ℝ}
variable (hΩ: ∃ f:I→ℝ, (∀ i, ¬ (R i ∧ i∈Set.range (Sum.elim J₀ J₁)) → Flame (Q.fill i) Pt (S i) (wrap c b) v n j (f i)) ∧ Ac.Hit S Pt.B f u A')
variable (hv:SumBudget (fun i=> l i*Real.exp (θ*coverNumber P.B (s i))) ν) (ha:0≤a₂)(hT:0 ≤ u)(hθ:a₂≤θ)(hξ:0≤z₀)(he:1≤ v)(hC:0 ≤ C)(hβ:0 ≤ ε₀)
local notation "C₁"=> z₀^(d+1)*C
local notation "X₀"=> C₁*ν
variable (hz : Real.exp ((a₂-θ)*(P.B:ℝ)) * (α*(z₀^(d+1)*C)) ≤ ε₁)
local notation "J'"=> {i:I// i ∉ Set.range J₀}
variable (hx:P.B= 0) -- remove
variable (hR:∀ i:E, R (J₁ i) → coverNumber P.B (s i) ≤ P.B →∀ (p:Label d), ActionTest H b (Q.fill (J₁ i)) p.val → wealth p.val Pt.threshold v ≤ ε₀*l i)
include hi hR hv hk ht hp he hξ hL hT hθ hD hA hΩ hβ hz ha hC
set_option maxHeartbeats 580000 in
lemma spare {s':ℝ} (hΦ₀:∀ i:Jars d,∃ t:ℝ, Flame (Q.fill (J₀ i)) Pt (S (J₀ i)) (wrap c b) v n j t ∧ t* Real.exp (u*coverNumber Pt.B (S (J₀ i))) ≤ a₀*z₀^(weightJ i)*princS x i P φ ∧ ∀ y:Label d,ActionTest H b (Q.fill (J₀ i)) y.val→∀ k:Rings d, weight k.val≤ weightJ i → ‖Stative.fare k y.val Pt.threshold v -(z₀:ℂ)^ weight k.val * Stative.fare k (gradeCut d i.val x).val Pt.threshold z‖ ≤ U₁*princS x i P φ) : Scenes q Q S J₀ H Pt P v s' φ z z₀ a₀ (X₀+A') u a₂ U₁ ((max ε₀ ε₁)*ν+α*A') x b n j :=by
   obtain ⟨g,hg,hA'⟩:=hΩ; let U (i:E):Prop:= R (J₁ i); have hl : Function.Injective J₁:=fun i j h=> Sum.inr.inj (@hi (.inr i) (.inr j) h); have hz' i: J₁ i∉ Set.range J₀:= by rintro ⟨b,e⟩; exact Sum.inl_ne_inr (@hi (.inl b) (.inr i) e)
   let X: {i: E// U i} → J':= fun i=>⟨J₁ i.val,hz' _⟩
   have hX:Function.Injective X:=fun i j h=>Subtype.ext (hl (congr_arg Subtype.val h)); let U'(i:J') := G i.val
   have hV(i:J'):i∉ Set.range X → U' i:=fun h hx=> by
       obtain ⟨hv1,p,hp⟩:=hx; rcases p with p|p; exact i.property ⟨_,hp⟩
       let H:J₁ p=i.val:=hp; let Z:{i:E//U i}:=⟨p,Eq.mp (congr_arg R H.symm) hv1⟩; exact h ⟨Z,Subtype.ext hp⟩
   have he'(i:I)(h:i∈Set.range J₁)(hh:R i):¬ G i:= fun hp=>hp ⟨hh, let ⟨q,hq⟩:=h; ⟨Sum.inr q,hq⟩⟩
   let f(i:J'):= if h:i∈Set.range X then (Za) (Classical.choose h).val else g i.val
   have hT0(i:{i:E//U i}): f (X i)= Za i.val:=by
       unfold f; split; next h=>rw [show Classical.choose _=i from hX (Classical.choose_spec h)]
       next h=> exact (h ⟨_,rfl⟩).elim
   have hf(i:J'): Flame (Q.fill i.val) Pt (S i.val) o v n j (f i):=by
       by_cases hb:i∈Set.range X; · obtain ⟨i,rfl⟩:=hb; rw [hT0]; exact hD i.val i.property
       unfold f; rw [dif_neg hb]; exact hg i.val (hV i hb)
   have hZ(g:J'→ℝ)(Z W:ℝ)(hp:SumBudget (fun i:{i:E//U i} => g (X i)) Z)(hv:SumBudget (fun i:{i:J'//i∉Set.range X}=>g i.val) W): SumBudget g (Z+W):=by
       let B:= {i:E//U i}; let T:= {i:J'//i∉ Set.range X}; let Z₀:B⊕T→J':=Sum.elim X Subtype.val; have he : Function.Bijective Z₀:=by
         constructor; intro i j h; rcases i with i|i <;> rcases j with j|j; exact congr_arg _ (hX h); exact (j.property ⟨_,h⟩).elim; exact (i.property ⟨_,h.symm⟩).elim; exact congr_arg _ (Subtype.ext h)
         intro i; by_cases ht:i∈Set.range X; · obtain ⟨x,rfl⟩:=ht; exact ⟨.inl _,rfl⟩
         exact ⟨.inr ⟨i,ht⟩,rfl⟩
       have ht:SumBudget (g∘Z₀) (Z+W):= Extra.Iteration.Cost.sum hp hv
       have hg (i:J'):0≤g i:=by obtain ⟨i,rfl⟩:=he.2 i; exact ht.1 _
       exact ⟨hg,(Equiv.summable_iff (Equiv.ofBijective Z₀ he)).mp ht.2.1, ((Equiv.ofBijective Z₀ he).tsum_eq g).symm.trans_le ht.2.2⟩
   have hK:= budget_pull (w:=fun i=>g i*Real.exp (u*coverNumber Pt.B (S i))) (fun i:{i:J'//i∉ Set.range X}=>i.val.val) (Subtype.val_injective.comp Subtype.val_injective) (Iris.hit_collect o S _ hA hA') -- args name inspect
   let Δ:=C₁; have hΦ:0 ≤ Δ:= mul_nonneg (pow_nonneg hξ _) hC -- shadow hΦ -> rename
   refine ⟨hA,hΦ₀,⟨f,hf,?_⟩,fun p h'=>?_⟩ -- fmt1 nested
   · apply hZ; swap; · convert! hK using 1; ext i; unfold f; rw [dif_neg i.property]
     refine budget_mono (budget_scale hΦ (budget_pull (Subtype.val (p:=U)) Subtype.val_injective hv)) (fun i=>mul_nonneg (hf _).sight.travels (Real.exp_nonneg _)) fun i=>?_
     rw [hT0]; dsimp only; let Y:= coverNumber P.B (s i.val); let V:= l i.val; have hr :0 ≤ V:=hL _; let p:ℝ:=u*b₀ (J₁ i.val);
     have hz: Δ * Real.exp (a₂ *Y-p)* V * Real.exp p=Δ*(V*Real.exp (a₂*Y)):=by rw [Real.exp_sub]; field_simp -- use exp positive
     exact hz.trans_le (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _))) hr) hΦ)
   apply hZ; swap; · refine budget_mono (budget_scale (zero_le_one.trans hk.light) hK) (fun i=>wealth_ge ..) (fun i=> ?_)
                     let j:=i.val; let x:=j.val; have he := hk.earn _ b _ _ _ _ _ _ ht hp (zero_lt_one.trans_le he) (hg _ (hV _ i.property)) (h' _); exact he.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (hg x (hV j i.property)).sight.travels (Real.one_le_exp (by positivity : 0 ≤ u * _))) (zero_le_one.trans hk.light))
   let W:=max ε₀ ε₁; refine budget_mono (budget_scale (hβ.trans (le_max_left ..)) (budget_pull (Subtype.val (p:=U)) Subtype.val_injective hv)) (fun i=> wealth_ge ..) fun i=>?_
   let I:=i.val; let z:=coverNumber P.B (s I); let V:= Real.exp (θ*z); have hi := i.property; have hW:=hL I; change wealth _ _ _ ≤ max _ _*(l I * V); have htθ:=ha.trans hθ; have hU:1≤V:=Real.one_le_exp (by positivity)
   by_cases hpz:z ≤ P.B
   · exact (hR _ i.property hpz _ (h' _)).trans (mul_le_mul (le_max_left _ _) (le_mul_of_one_le_right hW hU) hW (hβ.trans (le_max_left ..)))
   have he':= hD I hi; let H' :ℝ:= α; let E:ℝ:= Real.exp ((a₂-θ)*z); have hf:E ≤ Real.exp ((a₂-θ)*P.B):=Real.exp_monotone (mul_le_mul_of_nonpos_left (by exact_mod_cast Nat.le_of_lt (lt_of_not_ge hpz)) (by linarith))
   have hy': u* b₀ (J₁ I)≥0:= by positivity
   have hm: Real.exp (a₂*z-u*b₀ (J₁ I))≤ E*V:=by unfold E V; rw [← Real.exp_add]; apply Real.exp_monotone; linarith only [hy']
   apply (hk.earn _ b _ _ _ _ _ _ ht hp (zero_lt_one.trans_le he) he' (h' _)).trans
   change α*(Δ*Real.exp _*l I) ≤ _; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hΦ) (hL _)) (zero_le_one.trans hk.light)).trans ?_; rw [show α*(Δ*(E*V)*l I)=E*(α*Δ)*(l I*V) from (by ring)]; exact mul_le_mul_of_nonneg_right (((mul_le_mul_of_nonneg_right hf (mul_nonneg (zero_le_one.trans hk.light) hΦ)).trans hz).trans (le_max_right ..)) (mul_nonneg hW (zero_le_one.trans hU))
end Incidence
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.Incidence.spare
