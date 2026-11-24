import YM.Massive.PCAC.Sum
import YM.Massive.Jasper.Source
/-!
# Test consequence at fixed reference for the actual massive trajectories

Full bare scalar-meson Ward operation in the differentiation convention here
(in bare spacing units, uses *bare* mass difference BEFORE the emissions),
all the way through any number of cuts. Significant off-diagonal
susceptibility actually advances to the difference of `massRead` at the
reference; as a limit as momentum tends toward zero wave, including interacting
unmasked history, thus NONDEGENERATE. This is progress on relating the mass
signal to PCAC, not yet a physical field theorem. No normalization taken from
expecting nonvanishing in the *physical* quotient.

Also specifies exactly where instead the axial-sum measurement value would
need a *contact estimate* to transfer. Do not claim it (may be tested from
much shorter q windows than going all the way to depth N).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Lat Function Lattice Filter
open scoped Topology ComplexOrder
variable (C:Sequence)(a b: Flavor 6){ν η β d:ℝ}{r:Flavor 6→ℝ}

/-- Probe at any active m, with `scalarWard` including the bare mass difference. -/
def peeled(i m:ℕ) := let A:= C.A i; C.S.toStop (C.R i) A.β A.w (C.N i) m (A.regulator.density*scalarWard a b A.regulator)
def tilts(i:ℕ):= chord 1 a b (C.A i) 0 (peeled C a b i 0)
abbrev YT (i q:ℕ) := let A:= C.A i; C.S.toStop (C.R i) A.β A.w q 0 (axialSum a b g5 A q)
def axis(i q:ℕ):ℂ:= chord g5 a b (C.A i) 0 (YT C a b i q)
structure Gift (r:Flavor 6→ℝ)(d:ℝ): Prop where
   body (i:ℕ)(m:ℕ)(h:m≤ C.N i): 0 < Stiffness.body ((C.A i).density m) 1
   probe (a b:Flavor 6)(h:a≠b): Tendsto (tilts C a b) atTop (𝓝 ((r a-r b:ℝ) :ℂ)) ∧ ∀ᶠ i:ℕ in atTop, d/2 < ‖tilts C a b i‖
   axial (a b:Flavor 6)(h:a≠b)(q :ℕ→ℕ)(hx:∀ i,q i ≤ C.N i): ∃ M:∀ i j:ℕ, Deck (C.S.side (C.R i) j) 6, (∀ i,M i (q i)=0)∧ (∀ i j:ℕ, j< q i→ M i j=liftM (C.A i) g5 a b j (M i (j+1))) ∧
        Tendsto (fun i=> axis C a b i (q i) + 2*chord g5 a b (C.A i) 0 (passenger (M i 0))) atTop (𝓝 ((r a+r b:ℝ):ℂ))

theorem offers (hp:C.PathBand β ν η)(hr:C.Service r d):Gift C r d:=by
    refine ⟨fun i m hi=>(hp.compare hi).real.self_of_nhds,?_ ,?_⟩ -- notation check
    · intro a b h; have hx: Tendsto (tilts C a b) atTop (𝓝 ((r a-r b:ℝ):ℂ)):=by rw [Complex.ofReal_sub]; exact ((hr.tendency a).sub (hr.tendency b)).congr (fun i=> (PCAC.reference a b (C.A i) (hp.normalized i) h 0 (Nat.zero_le _)).symm)
      refine ⟨hx,hx.norm.eventually (lt_mem_nhds ?_)⟩; rw [Complex.norm_real]; change d/2 < |r a-r b|; linarith only [hr.margin,hr.leave a b h]
    intro a b h q hx; choose M hh hg H using fun i=>(charge a b g5 g5 (C.A i) (hp.normalized i) h g5_sq g5_sq (q i) (hx i) 0 (Nat.zero_le _)).2
    refine ⟨M, hh,hg,?_⟩; rw [Complex.ofReal_add]; apply ((hr.tendency a).add (hr.tendency b)).congr fun i=>?_; rw [show axis C a b i (q i)=_ from H i]; abel

lemma gifts {η ε:ℝ}(he:0<η)(hv:0<ε): ∀ᶠ β in atTop,∃ (C:Sequence)(d:ℝ)(r:Flavor 6→ℝ),0 <β∧ C.PathBand β ε η ∧ C.Service r d ∧ Gift C r d:=by
    filter_upwards [Sequence.travel he hv] with i hi; obtain ⟨C,d,r,h,hP,hT⟩:=hi; exact ⟨C,d,r,h,hP,hT,offers C hP hT⟩
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.gifts
