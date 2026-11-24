import YM.Sprig.Emit
/-! For any phase candidate on the fixed mixture W, retaining the same derivative fields, a polymer allowance for the undifferentiated kernels suffices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder Interval
variable {C:Sequence} {D d d' n:ℕ} (P:Calibration C)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV Vale Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF Massive.Elm.SparK.Arbor.PlaneG
variable (φ:ℕ→ℕ)(Q:Massive.Tarn.Choir)(hQ:Q.Harmony P φ)
open Function Set Finset Metric Compass
namespace Canopy
abbrev KForm(Q:Choir):=(n:ℕ)→ Points n→ MultilinearMap ℂ (fun _:Fin n=> Q.W) ℂ
structure Groom (Q:Choir)(S:KForm Q):Prop where
     nice(n:ℕ)(p:Fin n→ Q.W) :ContDiffOn ℝ ∞ (fun x=> S n x p) (conf n)
     arcs(n:ℕ)(p:Fin n→ Q.W)(x:Points n)(hx:x∈conf n)(i:Fin n)(a:Axis): YM.Analysis.D (Points.direction i a) (fun x=> S n x p) x= S n x (update p i (Q.arc a (p i)))
variable {P φ Q}(E:Canopy P φ Q)(S:KForm Q)
variable (x: Fin n→ Texts) (hx:∀ i,Loaded E (x i))
noncomputable abbrev dawnP (i:ℕ)(w:Fin n→ Q.W)(y:Points n):= S n ((E.B i).r • y) w
noncomputable abbrev risingH(i:ℕ)(y:Points n):= dawnP E S i (fun k=>act E i (x k)) y
-- eventual uniform bound per loaded text, with *some* power. visible N dependent allowed.Event.Sym.
structure Money :Prop where
     holds (n:ℕ)(x: Fin n→ Texts)(hx:∀ i,Loaded E (x i))(K:Set (Points n))(hk:IsCompact K)(hy:K⊆conf n):∃ m:ℕ,∃ A:ℝ,0 ≤ A ∧∀ᶠ i:ℕ in atTop, ∀ y∈ K, ‖risingH E S x i y‖ ≤ A*E.cc i^m
-- C.Proof formation. avoid circular Story.
variable (hS:Groom Q S)
local instance choir (n:ℕ):ContinuousSMul ℝ (Points n):= inferInstance
set_option maxHeartbeats 500000
include hQ hS
lemma infancy (k:ℕ)(p:Fin n)(a:Axis)(x:Points n)(v:Fin n→Q.W)(hx:x∈conf n):YM.Analysis.D (Points.direction p a) (dawnP E S k v) x= dawnP E S k (update v p (bright Q (E.B k).r a (v p))) x:=by
     let w:=(E.B k).r; let R:Points n→L[ℝ]Points n:= w • ContinuousLinearMap.id _ _; let Y(u:Points n):= S n u v
     have hp:R x∈ conf n:= vital P φ Q hQ x hx _ (E.B k).realH
     have h:= ((hS.nice n v).differentiableOn (by simp)).differentiableAt ((conf_open n).mem_nhds hp)
     change fderiv ℝ (Y ∘R) x _= _
     rw [fderiv_comp x h R.differentiableAt,R.fderiv]; change fderiv ℝ Y (R x) (w • Points.direction p a)= S n (R x) (update v p ((w:ℂ) • Q.arc a (v p)))
     rw [map_smul,(S n (R x)).map_update_smul]; exact congr_arg (fun z:ℂ=> (w:ℂ) • z) (hS.arcs _ v _ hp p a)
lemma livingZ(i j:ℕ)(p:Points n)(hp:p∈conf n): ContDiffAt ℝ (j: ℕ) (risingH E S x i) p:=by
     let z:= (E.B i).r; let R:Points n→L[ℝ] Points n:= z • ContinuousLinearMap.id _ _; exact ((((hS.nice n (fun k=> E.act i (x k))).contDiffAt ((conf_open n).mem_nhds (vital P φ Q hQ p hp _ (E.B i).realH))).of_le (show (↑(j:ℕ) : WithTop ℕ∞)≤ ∞ from (by exact_mod_cast (show ((j:ℕ): ℕ∞) ≤ ⊤ from le_top)) )).comp p R.contDiff.contDiffAt)
variable (H:Money E S)
open Massive.Fir.Gains
include H hx
omit H
local notation "X"=> Texts
local notation "σ" i:arg=>E.cc i
local notation "ω" i:arg=>E.V i
local notation "θ" i:arg=> E.act i
set_option quotPrecheck false
lemma puncture (j:Fin n)(b:Axis): let f(k:Stokes ((x j).1+2)):= update x j (lifted E k); ∃ T:ℝ,0 ≤ T ∧ ∃ g:ℕ→ Stokes ((x j).1+2)→ℂ, ∀ᶠ i in atTop, (∀ k, ‖g i k‖ ≤ T)∧∀ z∈conf n,YM.Analysis.D (Points.direction j b) (risingH E S x i) z=∑ k,g i k • risingH E S (f k) i z:=by
     intro w; obtain ⟨T,hP,g,hg⟩:= E.seconds (hQ:=hQ) (x j) (hx j) b
     refine ⟨T,hP,g,hg.mono fun i hi=>⟨hi.1,fun z hz=>?_⟩⟩; unfold risingH; change YM.Analysis.D _ (dawnP E S i (fun k=> E.act i (x k))) z= _; rw[infancy hQ E S hS i j b z (fun k=> act E i (x k)) hz, hi.2]; unfold dawnP; rw [MultilinearMap.map_update_sum]; apply Finset.sum_congr rfl; intro k _; rw [MultilinearMap.map_update_smul]; apply congr_arg; apply congr_arg; funext l; by_cases hp:l=j; · subst l; simp [w]; -- parser
     · simp only [w, Function.update_of_ne hp]
lemma tags(p:Fin n)(j:Stokes ((x p).1+2))(i:Fin n):Loaded E (update x p (lifted E j) i):=by
     by_cases h:i=p
     · subst i; rw [Function.update_self]; exact pays E j
     rw [Function.update_of_ne h]; exact hx i
include H
set_option maxHeartbeats 650000
lemma orbitWide (k:ℕ)(B:Fin k→ FrameI n) (K:Set (Points n))(hk:IsCompact K)(hs:K⊆conf n):∃ m:ℕ,∃ C:ℝ,0 ≤ C ∧∀ᶠ i in atTop,∀ y∈K, ‖iteratedFDeriv ℝ k (risingH E S x i) y (riot n ∘B)‖ ≤ C*E.cc i ^m:=by
     induction k generalizing x with
     | zero=> simpa only [iteratedFDeriv_zero_apply] using H.holds n x hx K hk hs
     | succ k ih=>
       let j:=(B 0).1; let b:=(B 0).2
       obtain ⟨T,hP,g,hg⟩:= puncture hQ E S x hx hS j b; let L:= Stokes ((x j).1+2); let f(l:L):=update x j (E.lifted l)
       choose m C hC Hc using fun l:L=> ih (f l) (tags hQ E S x hx hS j l) (Fin.tail B) -- args
       let M:ℕ:=∑ l:L,m l
       refine ⟨M,∑ l:L,T*C l,Finset.sum_nonneg fun l _=>mul_nonneg hP (hC _),?_⟩; filter_upwards [hg,eventually_all.mpr Hc] with i hi ht y hy
       let F(l:L):= risingH E S (f l) i; let p:= riot n ∘B; let v:= riot n ∘Fin.tail B; have hp(l:L):ContDiffAt ℝ (k:ℕ) (F l) y:= livingZ hQ E S (f l) hS i k y (hs hy)
       have hm:YM.Analysis.D (p 0) (risingH E S x i)=ᶠ[𝓝 y] ∑ l:L,g i l • F l:=by
              unfold p Function.comp; rw [amber]; filter_upwards [(conf_open n).mem_nhds (hs hy)] with z hz; rw [Finset.sum_apply]; exact hi.2 z hz
       have hu := (livingZ hQ E S x hS i (k+1) y (hs hy)); have hwj:= YM.Analysis.cons_inner hu (p 0) v; rw [show riot n ∘B=Fin.cons (p 0) v from (Fin.cons_self_tail p).symm] -- wrong var
       rw [hwj, (hm.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_sum_apply (u:=Finset.univ) (f:=fun l=>g i l • F l) (fun l _=> contDiffAt_const.smul (hp l)), ContinuousMultilinearMap.sum_apply]; apply (norm_sum_le ..).trans; rw [Finset.sum_mul]; refine Finset.sum_le_sum fun l _=>?_ ; rw[iteratedFDeriv_const_smul_apply (hp l), ContinuousMultilinearMap.smul_apply, norm_smul, mul_assoc]; exact mul_le_mul (hi.1 l) (le_trans (ht l y hy) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (E.charge i) (Finset.single_le_sum (fun l _=> Nat.zero_le _) (Finset.mem_univ _))) (hC _))) (norm_nonneg _) hP -- orientation pole.
lemma pricing (k:ℕ)(K:Set (Points n))(hk:IsCompact K)(hs:K⊆conf n):∃ m:ℕ,∃ C:ℝ,0 ≤ C∧∀ᶠ i:ℕ in atTop,∀ y∈ K,‖iteratedFDeriv ℝ k (risingH E S x i) y‖≤ C*E.cc i^m:= by
    let I:= Fin k→FrameI n; choose m V h H using fun i:I=> orbitWide hQ E S x hx hS H k i K hk hs
    let M:= ∑ i:I,m i; let T (i:I):ℝ:=∏ a:Fin k, ‖spurH n (i a)‖; have ht(i:I):0 ≤ T i:=Finset.prod_nonneg fun b _=> norm_nonneg _
    refine ⟨M,∑ i:I,T i*V i,sum_nonneg (fun _ _=>mul_nonneg (ht _) (h _)),?_⟩; filter_upwards [eventually_all.mpr H] with j hj y hy
    rw[sum_mul]; refine (windsor _ (fun i:I=>V i*E.cc j^M) (fun i=>?_)).trans_eq (sum_congr rfl (fun _ _=>(mul_assoc ..).symm))
    exact (hj i y hy).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (E.charge j) (Finset.single_le_sum (fun i _=> Nat.zero_le _) (Finset.mem_univ _))) (h i))
end Canopy
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Canopy.orbitWide
#print axioms YM.Intag.Sprig.Canopy.pricing
