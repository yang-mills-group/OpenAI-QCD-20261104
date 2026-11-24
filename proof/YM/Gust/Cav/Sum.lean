import YM.Ward.Sum
import YM.Gust.Cav.Plants
/- Variant of YM.Ward.Sum, for Spiral register. -/


/-!
# Raw charge sums after normalization P=cD

Input line values for all quotient labels. Finite-dimensional λ over filtered levels;
no Lie reps assumed. Prove jets from comm D at all arities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spiral.Ward
open Set Function Filter Analysis Table
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

abbrev SpinRows (S : Table L) := ∀ d : ℕ, Ortho.Skew →ₗ[ℝ] (S.Field d →ₗ[ℂ] S.Field d)

variable (W : DiffPlan S) (T : SpinRows S)

def turns (K : Ortho.Skew) (p : S.Tag) : S.Tag := ⟨p.1,T p.1 K p.2⟩

def disc (q : Fin n → S.Tag) (x : Points n) := S.useAt S x q

def angular (q : Fin n → S.Tag) (K : Ortho.Skew) (x : Points n) :=
    ∑ i, (disc (update q i (turns T K (q i))) x +
         ∑ b : Axis, M4.move K.val (x i) b • disc (update q i (rise W b (q i))) x)

def commutes := ∀ d (t : Ortho.Skew) b (p : S.Field d),
    W.deriv d b (T d t p)+ (∑ i : Axis, (t.val i b:ℂ) • W.deriv d i p)= T (d+1) t (W.deriv d b p)

def onLine (a : Axis) (x : Points n) := ∀ i : Fin n, ∃ t : ℝ, x i=t • basis a

def Collinear := ∀ (a : Axis) (n : ℕ) (K : Ortho.Skew) (q : Fin n → S.Tag) (x : Points n),
    x∈conf _ → onLine a x → angular W T q K x=0

lemma fromD (h : S.Hierarchy) (hp : W.Derivatives S) {x : Points n} (hx : x∈conf _) (i : Fin n) a (q : Fin n → S.Tag) :
    Analysis.D (Points.direction i a) (disc q) x=disc (update q i (rise W a (q i))) x := by
  rw [← show (fun y => S.useAt S y (update q i (⟨(q i).1,(q i).2⟩ : S.Tag))) = disc q from
    funext fun y => by rw [show update q i ⟨_,_⟩ = q from update_eq_self ..]; rfl]
  exact (W.derivative_slot hp h.laws.toSymmetric h.smooth hx i q (q i).2 a).symm

lemma cont_disc (h : S.Hierarchy) (q : Fin n → S.Tag) {x : Points n} (hx : x∈conf n) : ContDiffAt ℝ ∞ (disc q) x :=
    ((S.class_smooth S h.smooth q) _ hx).contDiffAt ((conf_open _).mem_nhds hx)

/-! Evaluate one tag at one slot, Heterogeneous, use arbitrary contexts. -/
private def dec {d k : ℕ} (h : d=k) : S.Field d→ₗ[ℂ] S.Field k := h ▸ LinearMap.id
private lemma dec_eq {d k : ℕ} (h : d=k) (p : S.Field d) : dec h p=cast (congr_arg (Field S) h) p := by subst k; rfl

def here (q : Fin n → S.Tag) (x : Points n) (i : Fin n) (d : ℕ) : S.Field d →ₗ[ℂ] ℂ := by
  classical
  let w (p : S.Field d) := update q i (⟨d,p⟩ : S.Tag)
  let t := w 0
  have hi : (t i).1=d := by simp [t,w]
  let f := (S.classMoment S (fun i => (t i).1) x).toLinearMap (fun i => (t i).2) i
  exact f.comp (dec hi.symm)

lemma takes (q : Fin n → S.Tag) (x) (i) (d : ℕ) (p : S.Field d) :
    here q x i d p = disc (update q i ⟨d,p⟩) x := by
  let t := update q i (⟨d,(0:S.Field d)⟩ : S.Tag)
  dsimp only [here]
  -- need classMoment heq congr, use d'= fixed
  have hi : d=(t i).1 := by simp [t]
  let V : S.Field (t i).1 := cast (congr_arg (Field S) hi) p
  have he : dec hi p = V := dec_eq ..
  let s := update (fun j => (t j).2) i V
  have hf : (fun j => (⟨(t j).1,s j⟩ : S.Tag))=update q i ⟨d,p⟩ := by
    funext j
    by_cases h : j=i
    · subst j; simp only [s,update_self]; exact Sigma.ext hi.symm (cast_heq _ p)
    simp [s,t,h]
  rw [← hf]; unfold disc useAt
  rw [LinearMap.comp_apply]; change ((S.classMoment S (fun i => (t i).1) x).toLinearMap _ i) (dec hi p)=_
  rw [he]; rfl
end YM.Spiral.Ward

