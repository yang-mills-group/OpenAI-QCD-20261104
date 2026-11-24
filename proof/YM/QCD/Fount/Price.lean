import YM.QCD.Fount.Cop
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort Octave
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Token Tidings Sienna QCD.Loom Fleet Cove Reggae
open scoped Topology ENNReal ContDiff BigOperators Classical
open Lat YM.Next.Free
open Jets.Touch Port Kit Run Bay Strut Leaf Tee Flume Garden Orbit LeafM AtomF Kings
variable {L:Side} {t a u r w b σ η s p:ℝ} {J k N:ℕ}{g f v z h:ℝ→ℝ}
local notation "T"=> coneK L a
lemma noteJ (ht:0<a)(j:ℕ) : Rate su L ((1/16)*j) (fun i=> letterP (T i) j):=by
       induction j with
       | zero=> simp only [letterP,zero_add, Finset.sum_range_one,Kit.toll,Nat.cast_zero,mul_zero]; exact Rate.const _
       | succ k ih=> apply ((ih.weaken (by push_cast; linarith)).add (pitchB ht (k+1))).congr; exact Eventually.of_forall fun i=> Finset.sum_range_succ ..
lemma chordP (ht:0<a) (l:ℕ)(Z B:ℝ) : Rate su L ((1/16)*l) (fun i=> chord (T i) B Z l):= by unfold chord clump; exact ((((noteJ ht l).mul_right _).mul_left _).mul_right _)
lemma pace (b :ℝ) (hh: Rate su L b f)(h:Rate su L 0 g) (i:ℕ):Rate su L b (fun j=> clump i (g j) (f j)):=by
   have he:=Rate.add (Rate.const 1) (((Rate.const 1).add h).mul_right 1); unfold clump; exact (((hh.mul_left _).mul (he.pow i)).weaken (by linarith))
lemma coveL (ht:0<a) (hh:Rate su L 0 g)(h:Rate su L 0 f)(hp:Rate su L 0 z)(hk:Rate su L 0 v) (b t s r:ℝ)(l N:ℕ) : Rate su L ((1/16)*l) (fun x=> levy (T x) b t s (g x) (f x) r (v x) l (z x) N):=by
   unfold levy; have hf:= Brim.bell (Brim.prep hp 2) (Brim.prep h 2); have hv := hk.add ((hh.mul_right (Fintype.card Lat.Fiber)).mul_right (chord t s r l)); exact (((hf.mul (chordP ht l r b)).weaken (by linarith)).add ((hv.mul_left _).weaken (by positivity)))
local notation "X"=> eaves su L
lemma bitL {H:ℝ→ℕ→ℝ}(h:∀ i:ℕ,Rate su L ((1/16)*i) (fun t=> H t i))(k:ℕ):∀ᶠ t:ℝ in atTop,∀ i:ℕ,i ≤ k → 3 ≤ i → H t i * (X t)^i ≤  betaF su t L^(-(35/32):ℝ):=by
    have hh (i:ℕ)(hi:3 ≤ i):∀ᶠ t in atTop,H t i*(X t)^i ≤ betaF su t L ^(-(35/32):ℝ):=by
        have he:= ((h i).mul ((edge su L).pow i)) (-(35/32):ℝ) (by have h:(3:ℝ) ≤ i:=(by exact_mod_cast hi); unfold vow; linarith)
        exact he.mono fun i hi=> (le_abs_self _).trans hi
    have hg (i:Fin (k+1)):∀ᶠ t:ℝ in atTop, 3≤ i.val → H t i.val*(X t)^i.val≤ betaF su t L^(-(35/32):ℝ):=by
       by_cases he:3 ≤ i.val; · exact (hh _ he).mono fun t ht _=> ht
       exact Eventually.of_forall fun t h=>(he h).elim
    filter_upwards [eventually_all.mpr hg] with x hx i hi hp using hx ⟨i,by omega⟩ hp
lemma hurtL (hp:0 < r)(ht:Rate su L 0 f)(hs:0 ≤ s)(N:ℕ):
    let M:=fun Y x c=> N*tollS Y 2 (3*(Y*(s*Real.exp (-r*c)))) * (eaves su L x)^2
    ∀ᶠ x:ℝ in atTop,∀ c:ℕ,Stores.till x  ≤  c→ 1 ≤  f x→M (f x) x c ≤  betaF su x L^(-(35/32):ℝ) :=by
    intro M; let g x:=f x; have he:= ((ht.mul ((Rate.cutoff (L:=L) (a:=-1) hp (G:=su)).mul_left s)).mul_left 3); have h:Rate su L _ (fun x=> M (f x) x (Stores.till x)):= ((((ht.pow 2).mul he).mul_left _).mul ((edge su L).pow 2)) -- syntactic
    filter_upwards [Delay.shift_pos su L, h (-(35/32)) (by push_cast; unfold vow; linarith)] with x hx hv c hc hP
    refine le_trans ?_ ((le_abs_self _).trans hv)
    unfold M tollS; have hS:0 ≤ f x:=zero_le_one.trans hP; have hh: -r*(c:ℝ) ≤ -r*(Stores.till x:ℝ):=mul_le_mul_of_nonpos_left (by exact_mod_cast hc) (neg_nonpos.mpr hp.le); gcongr _ * ((_ ^ _)* (3* (_ *(s*Real.exp ?_)))) * _
-- combine
abbrev lull (L:Side)(x:ℝ):= betaF su x L^(-(35/32):ℝ)
lemma tunes (L:Side):Rate su L (-(35/32)) (fun i=>lull L i+3*lull L i):= Rate.power.add (Rate.mul_left Rate.power _)
end YM.QCD.Fount
