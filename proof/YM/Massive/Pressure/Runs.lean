import YM.Massive.Pressure.Selector
import YM.Massive.RG.History

/-!
# Apply selector to a bare mass splitting ray and all the actual stops

Here ask for estimates only against the *true densities*. All bounds on
actual Z after scalar extraction (full spin and gauge integral), not on
Z calculated separately in possibly incompatible voices. Reuse the same steps,
choices and analytic-family realization.

Provides a reduction of `Bpressure` math: no selector costs/conditions remain
once we can supply these upper/pricing and lower common bounds. E.g. to
specialize, set the upper U to include the exponential and g powers in
`eq:Bpressure`, absorb into analytic multiplier, and take the lower L relative
to it. The pertinent quantity is their ratio, to cost exponentially in per-stop
volume. This theorem raises that ratio just to power 21 (no other vol loss).
This file does *not* prove those input analytic-family upper or common-real-mass
lower bounds, nor that we've achieved the trajectories, spin mass estimates,
stability under splitting, primary/Ward read, etc., where it will be used.
Conditional **step**, not a construction of the physical scaling-trajectory.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive.Pressure
open Set Function Filter QCD QCD.Lat QCD.Grass NormedSpace Lattice Wilson
open scoped Topology ComplexOrder BigOperators

namespace Ray

variable {F N : ℕ} {n : Side}
variable (R : Side) (S : Scheme) (β w : ℕ → ℝ) (u v : Flavor F → ℝ)

def path (x : ℝ) : Flavor F → ℝ := u + x • v

def mass (n : Side) (z : ℂ) : Insertion n F :=
   ContinuousMap.const _ (exp (z • form (Onsite.offset v (Finset.univ : Support n))))

theorem ready (x : ℝ) : (S.wilson R β (path u v x) N).density =
    (S.wilson R β u N).density * mass v _ (x:ℂ) := by -- arg order?
    ext1 U
    let T := S.wilson R β (path u v x) N
    let W := S.wilson R β u N
    let D := Onsite.offset v (Finset.univ : Support (S.side R N))
    have he : T.D U=W.D U+(x:ℂ) • D := by
      rw [Onsite.unmasked T, Onsite.unmasked W, add_assoc]; congr 1
      ext i j; by_cases h : i=j <;>
        simp [D,path,T,W, Scheme.wilson, Onsite.offset,h]
    change T.density U=W.density U * _
    rw [Regulator.density_apply,he,gauss_add,Regulator.density_apply,smul_mul_assoc]
    have hx : form ((x:ℂ) • D)=(x:ℂ) • form D:= by unfold form; simp [Finset.smul_sum, smul_smul]
    rw [show gauss ((x:ℂ) • D)= exp _ from congr_arg exp hx]; rfl

def top (N : ℕ) (z : ℂ) : Insertion (S.side R N) F :=
    (S.wilson R β u N).density * mass v _ z

def Z (N i : ℕ) (z : ℂ) := joint ⇑(S.toStop R β w N i (top R S β u v N z))

lemma lands (x : ℝ) (i : ℕ) : Z R S β w u v N i x = joint ((S.run R β w (path u v x) N).density i) := by
    change joint _ = joint ⇑(S.toStop _ _ _ _ _ (S.wilson R β (path u v x) N).density); rw [ready]; rfl

lemma entry (z : ℂ) : Z R S β w u v N N z=(S.wilson R β u N).raw (mass v _ z) := by
    rw [Z,Scheme.entrance]; rfl
lemma hol : Differentiable ℂ (Z R S β w u v N N):= by
    let C := S.wilson R β u N
    let A : Fields (S.side R N) F →ₗ[ℂ] ℂ := C.raw.comp (show Fields (S.side R N) F →ₗ[ℂ] Insertion (S.side R N) F from
     { toFun := ContinuousMap.const _, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
    let D := form (Onsite.offset v (Finset.univ : Support (S.side R N)))
    have he : Z R S β w u v N N= A.toContinuousLinearMap ∘ (fun z:ℂ=> exp (z • D)):=funext fun z=> (entry ..)
    rw [he]
    exact A.toContinuousLinearMap.differentiable.comp (differentiable_exp_smul_const ℂ D)

lemma moves (i : ℕ) (h : i ≤ N) : Z R S β w u v N i =
    fun z=> S.multiplier R w i N F * Z R S β w u v N N z := funext fun z => by
      apply S.conservation R (fun k=> ⇑(S.toStop R β w N k (top R S β u v N z))) 0 (A:=S.run R β w u N)
        (S.carried R β w (top R S β u v N z) u) h (Nat.zero_le _)

open Disk

variable (hw : ∀ i<N,0 < w i)
variable (U L : ℕ → ℝ) (Y : ℕ → ℂ → ℂ) -- Y all scalars pulled at that stop (nonvanishing)
variable (M : Set ℕ)
/-- Bpressure inputs. Upper analytic-family estimate on extracted integral,
lower only at zero marker (e.g. paired masses as in supplied proof).
Specify any subset M of stops at that depth. -/
structure Budget (N : ℕ) : Prop where
   live i (h : i∈M) : i≤N
   upper_cost i (h : i∈M) : 0 < U i
   radius i (h : i∈M) : 0 < L i
   scalar i (h : i∈M) : DifferentiableOn ℂ (Y i) D ∧ ContinuousOn (Y i) closedD
   zeroFree i (h : i∈M) : ∀ x∈closedD, Y i x ≠ 0
   paid i (h : i∈M) : ∀ x∈closedD, ‖Z R S β w u v N i x / Y i x‖ ≤ U i
   common i (h : i∈M) : U i*L i ≤ ‖Z R S β w u v N i 0 / Y i 0‖

variable {Y M U L}
variable (he : Budget R S β w u v U L Y M N)
include hw he

lemma jointFit (i : M) : let f (i : M) x := Z R S β w u v N i x / Y i x / (U i:ℂ)
                           ∃ g, Joint i f g:=by
   intro f
   let c (i:M) := S.multiplier R w i.val N F
   let k := Z R S β w u v N N
   let r (i:M) (x:ℂ):=c i / Y i x / (U i:ℂ)
   have hc (i:M) : c i ≠ 0:=(S.positive R w hw (he.live i i.property) F).ne'
   have ht (j : M) : (U j:ℂ)≠0:= Complex.ofReal_ne_zero.mpr (he.upper_cost j j.property).ne'
   have hF (i:M) x:f i x=r i x*k x:=by
      unfold f; rw [moves R S β w u v i (he.live _ i.property)]
      unfold r c k; ring -- check
   have hu i : ∀ x∈closedD,r i x≠0 := fun x hx=> div_ne_zero (div_ne_zero (hc _) (he.zeroFree i i.property x hx)) (ht i)
   have hv (i:M):ContinuousOn (r i) closedD:=(continuousOn_const.div (he.scalar i i.property).2 (he.zeroFree i i.property)).div_const _
   refine ⟨fun m x=> r m x/r i x,⟨fun m=> ?_,fun m=> (hv m).div (hv i) (hu i), fun m x hx=> div_ne_zero (hu m x hx) (hu i x hx), fun m x hx=> ?_⟩⟩
   · have hh : DifferentiableOn ℂ (r m) D := ((show DifferentiableOn ℂ (fun _=> c m) D from (differentiable_const _).differentiableOn).div (he.scalar m m.property).1
                   (fun x hx=> he.zeroFree m m.property x (open_closed hx))).div_const _
     refine ⟨?_,?_,fun x hx=>?_⟩
     · rw [funext (hF m)]; exact hh.mul (hol R S β w u v).differentiableOn
     · rw [funext (hF m)]; exact (hv m).mul (hol R S β w u v).continuous.continuousOn
     unfold f; have h := he.upper_cost m m.property; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg h.le,div_le_one h]; exact he.paid m m.property x hx
   rw [hF m x,hF i x]; field_simp [hu i x hx]

theorem pressure (h : M.Nonempty) : ∃ x ∈ Set.Icc (1/2:ℝ) 1, ∀ m∈ M,
     let X := S.run R β w (path u v x) N
     U m * L m ^ 21 ≤ ‖joint (X.density m) / Y m x‖ ∧ ‖joint (X.density m) / Y m x‖ ≤ U m := by
     rcases h with ⟨i,hi⟩; obtain ⟨g,hg⟩:= jointFit R S β w u v hw he ⟨i,hi⟩
     let f m x := Z R S β w u v N m x / Y m x / (U m:ℂ)
     have hs(z:ℂ)(i:ℕ)(h:i∈M): ‖f i z‖= ‖Z R S β w u v N i z / Y i z‖ / U i:=by unfold f; rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (he.upper_cost i h).le]
     have ht(i:ℕ)(h:i∈M): L i ≤ ‖f i 0‖:=by rw [hs 0 i h]; apply (le_div_iff₀ (he.upper_cost i h)).mpr; rw [mul_comm]; exact he.common i h
     obtain ⟨x,hx,H⟩:= hg.selects (norm_pos_iff.mp ((he.radius i hi).trans_le (ht i hi)))
     refine ⟨x,hx,fun m hm=>?_⟩; intro X; dsimp only [X]; rw [← lands R S β w u v x];
     have hu : (x:ℂ)∈closedD:= by rw [closed,Complex.norm_real,Real.norm_of_nonneg ((by norm_num : (0:ℝ)≤1/2).trans hx.1)]; linarith [hx.2]
     refine ⟨?_, he.paid m hm x hu⟩
     have hl:= (pow_le_pow_left₀ (he.radius m hm).le (ht m hm) 21).trans (H ⟨m,hm⟩)
     change L m ^ 21 ≤ ‖f m x‖ at hl
     rw [hs x m hm, le_div_iff₀ (he.upper_cost m hm)] at hl; rwa [mul_comm]
end Ray
end YM.Massive.Pressure
#print axioms YM.Massive.Pressure.Ray.pressure
