import YM.Eden.Yurt
import YM.Elms.Corner
/-! # internship. projection normalized currency. Clock.after selection only through actual.Strata -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Evo
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free YM.Bloom YM.Arise YM.Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator TensorProduct Classical
variable {G:Gauge}{d k i m j l w r g q:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Cove Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.Gallery Elm.SparK.Arbor.PrismD Poised Papyrus Lining
open Poised.Plans RP YM.Source YM.Source.Drops QCD.Anomaly QCD.Creek YM.Eden Girdle Sieve Counting Counting.Terrain Pipes Facets Orientation MassiveQCD.Plate Carte.Hem Permit
-- economic.
variable {Q:SourceRead.TaperHol}
structure Coin (r l w i j:ℕ) (x:Drape) (g s:ℕ)(C Z:ℝ) : Prop where
   H : ∀ (P:BudgetPoint)(f:Side)(b:Cover)(v:ℝ),0<v → P.power=w → P.order=l→ 2*(r+1)< f.val → Flame (x f b) P (pot (r+1) f b) (wrap f b) v i j (C*levy g s P.threshold v)
   K : ∀ (P:Side)(b:Cover)(v:ℝ),0<v→∀ V:Grid P,load (fun _=>v) (x P b V) ≤ v^s*Z
variable {X Y:Drape}{Z C C' Z':ℝ}{v u:Mini d}
lemma merchant (h:Survey Q X g q v): ∃ Z:ℝ, 0 ≤ Z ∧∀ᶠ r:ℕ in Filter.atTop, ∀ l w i j:ℕ,∃ C:ℝ, 0≤ C ∧ Coin r l w i j X g q C Z:=by
      obtain ⟨Z,hz,H⟩:=Gallery.lantern X g q h.paid; refine ⟨Z,hz,?_⟩; filter_upwards [lease_flame _ _ _ h.paid] with r h l w i j; obtain ⟨C,hC,h⟩:=h l w i j; exact ⟨C,hC,⟨h,fun i z v hv U=> H v hv i z U⟩⟩
lemma Coin.raise (h:Coin r l w i j X g q C Z)(hr:C≤ C')(ht:Z≤Z'):Coin r l w i j X g q C' Z':=by
    constructor; · intro P f b v hv hw hk hp; apply Facets.leFlame (h.H P f b v hv hw hk hp); gcongr; unfold levy; positivity [P.threshold_pos]
    intro f b v hv U; exact (h.K f b v hv U).trans (mul_le_mul_of_nonneg_left ht (by positivity)) -- parser fix
-- labels.Anchor. η>0. χ= kappa^-1 Pr.Contour.Z.We.Motion.
def Ten (n i j:ℕ)(W η t v:ℝ):ℝ:= W^n * η^i * levy i j t v
noncomputable def doll (n i j:ℕ)(W η t v:ℝ) (P:Drape) : Drape:= ((Ten n i j W η t v:ℂ))⁻¹ • P
lemma dollar0 (n i j:ℕ){W η t v:ℝ}(hW:0<W)(hη:0<η)(ht:0<t)(hv:0<v) : 0<Ten n i j W η t v:=by unfold Ten levy; positivity
-- actual combinations from voucher
noncomputable def warpP(k:ℕ)(q:ℕ)(t v:ℝ)(u:Drape):Drape:= (↑(levy k q t v):ℂ)⁻¹ • u
variable (S:SourceRead.TaperHol)(p:Bard d)(j k:ℕ)
local notation "Tp"=> wide d 1 p
local notation "Xq"=> oink d k j
local notation "arm"=> raysL (d:=d) k j
noncomputable def weaveT (k i:ℕ)(q:Pad d)(η t v:ℝ)(c:ℂ) : ℂ:= c*((((η*t)^q.1.length *v^q.2.length/((η*t)^k*v^i)):ℝ):ℂ)
variable {Y:Bed}{u':ℕ}{X':Train u'} (W η:ℝ) (hP:(milky 0 Y c (G:=su) (d':=d)).IsSymm)
lemma credit0 (W η t v:ℝ)(hW:0<W)(hη:0<η)(ht:0<t)(hv:0<v)(u:Pad d→ℂ)(b:ℕ)(X:Drape)(G:Pad d→Drape) :
    doll b k j W η t v ((W:ℂ)^b • ((η:ℂ)^k • X + ∑ i∈ Xq,u i • ((η:ℂ)^i.1.length • G i))) = warpP k j t v X +∑ i∈Xq,weaveT k j i η t v (u i) • warpP i.1.length i.2.length t v (G i):=by
     unfold doll warpP weaveT Ten; simp only [levy, Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,mul_inv]; let e:ℝ:= t
     have ha:(v:ℂ)≠0:=by exact_mod_cast hv.ne'
     have hb:(t:ℂ)≠0:=by exact_mod_cast ht.ne'
     have hh:(η:ℂ)≠0:=by exact_mod_cast hη.ne'
     have ht':(W:ℂ)≠0:=by exact_mod_cast hW.ne'
     simp only [smul_smul,smul_add, Finset.smul_sum]; apply congr_arg₂ (·+·); · congr 1; field_simp
     refine sum_congr rfl (fun i _=>?_); congr 1; field_simp; ring
lemma weave_amt (t v:ℝ)(u:Pad d→ ℂ)(M Z:ℝ)(hη: M≤η*t)(hp:M ≤ v)(ht:1≤ M)(h: ∑ i∈ Xq,‖u i‖ ≤ Z): ∑ i∈ Xq, ‖weaveT k j i η t v (u i)‖≤ Z/M :=by
    let X:=η*t; have hh:X>0:= lt_of_lt_of_le (zero_lt_one.trans_le ht) hη; have hc:=lt_of_lt_of_le (zero_lt_one.trans_le ht) hp; have hM:=zero_lt_one.trans_le ht; have hx:1≤ X:= ht.trans hη; have hv:1≤ v:= ht.trans hp
    have hr(i:Pad d)(hi:i∈ Xq): M*(X^i.1.length*v^i.2.length) ≤ X^k*v^j:=by
         have hv' : i∈ arm:= (Set.Finite.mem_toFinset (raysR d k j)).mp hi
         let m:= i.1.length; let n:=i.2.length; obtain ⟨hu,hd,hq⟩ := hv'; have hQ:m < k ∨ n < j:=by unfold m n; omega
         rcases hQ with h|h
         · rw [←mul_assoc]; apply mul_le_mul _ (pow_le_pow_right₀ hv hd) (by positivity) (by positivity); exact (mul_le_mul_of_nonneg_right hη (pow_nonneg hh.le _)).trans (show X*X^m ≤ _ from (by rw [← pow_succ']; exact pow_le_pow_right₀ hx h)) -- X implicit
         rw [mul_left_comm M]; apply mul_le_mul (pow_le_pow_right₀ hx hu) _ (by positivity) (by positivity); exact (mul_le_mul_of_nonneg_right hp (pow_nonneg hc.le _)).trans (show v*v^n ≤ _ from (by rw [← pow_succ']; exact pow_le_pow_right₀ hv h))
    rw [le_div_iff₀ hM,mul_comm, Finset.mul_sum]; apply le_trans _ h; refine sum_le_sum fun i hi => ?_; rw [weaveT,norm_mul,Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ X^_*v^_/ _ from (by positivity)),mul_left_comm]; apply mul_le_of_le_one_right (norm_nonneg _); rw [← mul_div_assoc, div_le_one (by positivity)]; exact hr i hi
end YM.Massive.Evo
#print axioms YM.Massive.Evo.merchant
#print axioms YM.Massive.Evo.credit0
#print axioms YM.Massive.Evo.weave_amt
