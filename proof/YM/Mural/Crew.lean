import YM.Mural.Army
import YM.Mural.Clan
import YM.Mills.Seals
/-! # E kernels at an open lantern. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cupola
open QCD QCD.Grass QCD.Creek Cupola QCD.Cove QCD.Sway QCD.Sway.OrbitG Function Finset Filter MeasureTheory NormedSpace
open Plate Stitch Tablet Ribbon Lattice Wilson Lat RG Twist PaletteT
open scoped BigOperators Topology Classical ContDiff
variable {I D:Type}[Fintype I]{c:Side}(N:ℕ) (p:I→ Site c)(θ v t:ℝ)(q:I→Bool)
local notation "M"=> ample N I
local notation "R"=> Spine I
local notation "K"=> Keys c N
variable (G: Patron.Gem c (ample N I) D)(Ω:D→Finset I) (A:Set (Finset I))(Z:Support c)
variable (hΩ:∀ i U,Mint N p v q (Ω i) (G.view i U)) (hV:G.Gather) (he:∀ i,(Ω i).Nonempty → Z ⊆ (G.addr i).support)
local notation "F"=> Reel.render N p v θ G Ω A
include hΩ hV he
lemma began (hv:0<v) : Twist.Pillars (F) p q Z:=by
   let e:=(turn I (D:=K) θ).comp (withdraw N p v)
   refine ⟨fun i=> i.2.2.1,fun i=>i.2.2.2,fun i=>e.toLinearMap.toContinuousLinearMap.measurable.comp (hV.reads _),fun i x y hh=>congr_arg e (hV.sees _ x y hh),fun i U=>⟨cloak θ (Ω i.val) _ q (hΩ i.val U).shows,?_⟩,fun i=> he i.val i.2.2.1⟩
   intro j; change pluck K j ((turn I θ) (withdraw N p v (G.view i.val U)))∈_; rw [turned]; exact hopeful N θ _ _ (pennied N p v j _ _ (hV.role i.val U))
omit hΩ hV he
open QCD.Mural Patron Loom Kites
lemma boreY (e:ℝ)(hv:0<v)(he:0<θ)(h:1 ≤e)(hx:θ*t≤v)(hT:0<t)(n:ℕ) (x:Patio (Keys c N⊕Spine I))(s:Finset I)(hz:Polite q s x): premiumE c N I t e n ((turn I θ) x) ≤ premiumE c N I v e n x:=by
   rw [attachedM c N I t e n hT _ (cloak θ _ _ _ hz),attachedM c N I v e n hv x hz]
   change repay univ _ n _ (pluck K (burst q s) ((turn I θ) x)) ≤ repay univ e n _ (pluck K _ x); rw [turned]; rw [Mural.sheet _ _ _ _ h (fun _=> hT),Mural.sheet _ _ _ _ h (fun _=>hv)]; apply sum_le_sum; intro i _; simp_rw [ticket_mono (fun _=>t) i (fun _=>hT),ticket_mono (fun _=>v) i (fun _=>hv),prod_const]
   rw [fundW,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg he.le]; -- reorder
   let P:=premium (univ:Finset K) e n i; let y:=‖coef i (pluck K (burst q s) x)‖
   change P*(θ^i.card*y)*t^i.card ≤ P*y*v^i.card
   rw [show P*(θ^i.card*y)*t^i.card=P*y*((θ*t)^i.card) from (by rw [mul_pow];ring)]
   exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos he hT).le hx _) (mul_nonneg (premNN _ _ _ h) (norm_nonneg _))
include hΩ
open Push.AbsoluteSums
lemma bidsM (e r ε α:ℝ)(i n:ℕ)(he:1≤e)(hp:0<t)(h:0<θ)(hv:θ*t ≤ v) (g:D→ℝ) (hG: Ac.Hit (fun j=>(G.addr j).support) i g α ε)(hP:∀ i U, premiumG c N I v e n (letters G r U i) ≤ g i) :
    ∃ u: Reel.Answer N p G Ω A →ℝ,(∀ i U,premiumE c N I t e n (Reel.mist F r i U) ≤ u i) ∧ Ac.Hit (fun j=>((F).addr j).support) i u α ε:=by
     refine ⟨g∘Subtype.val,fun i U=>?_,fun v=> budget_pull (Subtype.val:Reel.Answer N p G Ω A→D) Subtype.val_injective (hG v)⟩
     rw [Reel.currentS]; let x:= letters G r U i.val; let Jx:= Ω i.val; have hZ:= Reel.mast (t:=r) N p q v G Ω hΩ U i.val -- argument implicit.K edit
     apply (boreY N θ v t q e ((mul_pos h hp).trans_le hv) h he hv hp n _ Jx hZ.shows).trans; rw [mintAlt c N I p v e n (Ω i.val) ((mul_pos h hp).trans_le hv) _ hZ]; exact hP ..
end YM.MassiveQCD.Cupola
#print axioms YM.MassiveQCD.Cupola.bidsM
