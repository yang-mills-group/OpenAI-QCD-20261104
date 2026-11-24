import YM.QCD.Cove.Crew
import YM.RG.Activities
/-! # format of scalar/Grassmann sector mixtures
Support overlaps on measured flags, not clipping cutoff.
Full comp sym and renorm conditions set separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cove
open Function Creek Grass Lat Finset MeasureTheory Metric NormedSpace
open Kit Wilson Lattice RG
open scoped Topology BigOperators ContDiff ComplexOrder Classical

abbrev Keys (n:Side)(F:ℕ):= Pairs (Modes n F)
abbrev EvenA (n: Side)(F:ℕ):= Patio (Keys n F)
variable {n f c:Side}{F:ℕ}
def locationP : Keys n F→ Site n:= Sum.elim (fun i=>i.1.1) fun i=>i.1.1
def limits (A:Support n): Finset (Keys n F) := univ.filter fun i=>locationP i∈A

def Gated (A: Support n)(U:EvenA n F):= light (Keys n F) U ∈ region (limits A)
def Decor (S:Ratio c f)(A:Support f)(U:EvenA c F):= light (Keys c F) U∈ region (univ.filter fun i=> S.embed (locationP i)∈A)
def shadeG (F: Grid n→EvenA n F) : Prop:=∀ U(g: Frame n), slots _ g (light _ (F (gauge g U)))=light _ (F U)
variable (S:Ratio c f)
structure Hat (n:Side) where
 place: Support n
 inv : Support n
 alive : inv.Nonempty
 part : inv⊆place
open NormedSpace
structure Rise (n:Side)(F:ℕ) (E J:Type) where
 row : E → RegularAddress n
 front : J→ Hat n
 main : E→ Grid n→ EvenA n F
 plug : J→ Grid n→ EvenA n F
variable {S}
variable {E J : Type}
namespace Rise
variable (p: Rise n F E J)(t : ℝ)
-- Carry payload, evaluations use exactly these masks and actual flags
structure Wave :Prop where
 use i : LocalOn (p.row i).support (p.main i)
 appear i U : Gated (p.row i).support (p.main i U)
 measure i: Measurable (p.main i)
 oblige i: UsesFinal t (p.front i).place (p.plug i)
 chair i U: Gated (p.front i).place (p.plug i U)
 budget i: Measurable (p.plug i)
 permits i U: (p.plug i U) ≠ 0 → RG.flags t U ∩ (p.front i).place=(p.front i).inv

structure Reframe : Prop where
 main : ∀ i,shadeG (p.main i)
 plug : ∀ i,shadeG (p.plug i)



def reading (U : Grid n) (i:E) : EvenA n F := masked t (p.row i).support (p.main i) U
def hyp (U:Grid n) : EvenA n F :=∑' i,p.reading t U i

def wish (K:Finset J): Support n:=K.biUnion fun i=> (p.front i).inv
def spare (K : Finset J) := (↑K:Set _).Pairwise fun i j=> Disjoint (p.front i).place (p.front j).place

def dusk (U : Grid n) (J' : Finset J): EvenA n F:= if p.spare J'∧ p.wish J'=flags t U then ∏ i∈J',p.plug i U else 0
def tint (U:Grid n): EvenA n F:=∑' J',p.dusk t U J'
def bluff (U:Grid n) : Fields n F:=light _ (exp (p.hyp t U) * p.tint t U)

lemma hype (i:E)(U):p.reading t U i=if Healthy t (p.row i).support U then p.main i U else 0:=by unfold reading; split <;> next h=> first| exact masked_eq _ _ _ _ h| exact masked_ne _ _ _ _ h -- uses .. notation maybe
lemma readable (h:p.Wave t)(i:E)(U): Gated (p.row i).support (p.reading t U i):=by rw [hype]; split; exact h.appear .. ; unfold Gated; rw [map_zero]; exact Subalgebra.zero_mem _
@[fun_prop] lemma ready (h : p.Wave t)(i:E): Measurable (fun U=>p.reading t U i) := masked_measurable _ _ _ (h.measure i)
@[fun_prop] lemma blurry [Countable E][Countable J] (h:p.Wave t): Measurable (p.bluff t):=by
  haveI : SecondCountableTopology (Patio (Keys n F)):=inferInstance
  have he: Measurable (p.tint t):=by
    unfold tint; apply Measurable.tsum -- signature
    intro i
    have hi : MeasurableSet {U : Grid n|p.spare i ∧ p.wish i=flags t U}:=by
      by_cases hg:p.spare i; · simp only [hg,true_and,eq_comm]; exact flags_measurable_eq ..
      simp [hg]
    unfold dusk; apply Measurable.ite hi ?_ measurable_const
    exact Finset.measurable_prod _ fun j _=> h.budget j
  have hf : Measurable (p.hyp t):= Measurable.tsum (fun i=> ready p t h i)
  have hm:=lightC (Keys n F)
  exact hm.measurable.comp (((exp_continuous.measurable.comp hf)).mul he)

end Rise
end YM.QCD.Cove
