import YM.Plateau.Belt
import YM.Plateau.Curl
/-
All shape rotations use public label metric at reference, get uniform before L.
We exploit existence of an invariant core from ANY earlier shelf.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Sprig
open Function Filter Set MeasureTheory QCD.Sway
open Massive QCD QCD.Lat QCD.Grass Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open YM.Fir Massive.Fir Choir Pollens HarmonyF YM.Intag.Sprig YM.Intag.Sprig.Canopy Chloe
open Poised Plans Plans.Stamp Poised.Stative
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d:ℕ}(T: Pollens P Q)(E: Canopy P φ Q)
variable (hP:P.System)
variable (n: Side)(he:Injective (P.candidate d n 0))
open Massive.Oriole
open LinearMap
-- character tags. NoneSigned vac flavor.L upstairs.C.Cal.T.
abbrev Vein (g:Bool):= {p : (EuPin × Signed × ℂ) // p.1.Lifts p.2.1 ∧ Massive.Oriole.conjug p.1 (pulp g)= p.2.2 • pulp g}
abbrev Vesta (g t:Bool):= FlavorTorus ⊕ (Vein g × {k:Unit // t=true})
variable (p q:Flavor 6)(g t:Bool)(sym:RawSym)
noncomputable abbrev viewS (d:ℕ)(i: Vesta g t): Label d≃ₗ[ℂ]Label d:= Sum.elim (sym.flavor d) (fun x=> sym.pin d x.1.val.1) i
noncomputable def quip (i:Vesta g t):ℂ:=Sum.elim (UV.paidM p q) (fun i=> i.1.val.2.2) i
local notation "Cq"=> quip p q g t
noncomputable def bluff (d:ℕ) : Submodule ℂ (Label d) where
    carrier:={x| CharmC p q x.val ∧ (t=true → Wings g x.val)}
    zero_mem' :=by refine ⟨fun i=>?_,fun _ i s _ z _=>?_⟩; all_goals change (_ : Pol d)=_; all_goals apply Eq.trans (map_zero _) (smul_zero _).symm
    add_mem' := by
       intro x y ⟨hx,hu⟩ ⟨hp,hq⟩; refine ⟨fun i=> ?_,fun h i s hl z hv=>?_⟩; · exact (map_add ..).trans ((congr_arg₂ HAdd.hAdd (hx i) (hp i)).trans (smul_add ..).symm)
       exact (map_add ..).trans ((congr_arg₂ HAdd.hAdd (hu h i s hl z hv) (hq h i s hl z hv)).trans (smul_add ..).symm)
    smul_mem' := by
       intro c x ⟨hp,hq⟩; refine ⟨fun i=>?_,fun h i s hl z hv=>?_⟩; · exact (map_smul ..).trans ((congr_arg (c • ·) (hp i)).trans (smul_comm ..))
       exact (map_smul ..).trans ((congr_arg (c • ·) (hq h i s hl z hv)).trans (smul_comm ..))
lemma gateL (x:Label d) : x∈ bluff p q g t d↔∀ i,viewS g t sym d i x=quip p q g t i • x:=by
      constructor
      · intro ⟨hp,hq⟩ i; apply Subtype.ext; rcases i with i | ⟨j,s,h⟩
        · exact (sym.flavorActs d i x).trans (hp i)
        exact (sym.pinActs d _ x).trans (hq h _ _ j.prop.1 _ j.prop.2)
      intro h; refine ⟨fun i=> ?_,fun ht i s hp z he=>?_⟩
      · rw [←sym.flavorActs]; exact congr_arg Subtype.val (h (.inl i))
      rw[←sym.pinActs]; exact congr_arg Subtype.val (h (.inr (⟨⟨i,s,z⟩,⟨hp,he⟩⟩,⟨(),ht⟩)))
private lemma belongs (i : Vesta g t)(G:RawSym)(x:Label d) : viewS g t sym d i x=viewS g t G d i x:=by
      apply Subtype.ext; cases i <;> first|exact (sym.flavorActs ..).trans (G.flavorActs ..).symm | exact (sym.pinActs ..).trans (G.pinActs ..).symm
variable (d)
structure Ami (Z:Label d→ₗ[ℂ]Label d):Prop where
     root x : Z x∈ bluff p q g t d
     same x: x∈ bluff p q g t d→ Z x=x
     pays (U:Submodule ℂ (Label d))(s:RawSym)(h:∀ x i,x∈U ↔ viewS g t s d i x∈U): (∀ x∈U,Z x∈U)∧(∀ x,(∀ i,viewS g t s d i x-(quip p q g t i) • x∈ U)→ x-Z x∈U)
include he hP
lemma nature :∃ Z:Label d→ₗ[ℂ]Label d,Ami d p q g t Z:=by
    let e:InnerProductSpace.Core ℂ (Label d):={
        inner:=Chloe.pollen P n
        conj_inner_symm x y:= Chloe.sparks P n y x
        re_inner_nonneg x:= Chloe.pp0 P n x
        add_left x y z:= Chloe.timely P n x y z
        smul_left x y r:= Chloe.money P n r x y
        definite x h:=by by_contra hp; exact (Chloe.ppU P n x he hp).ne' (congr_arg Complex.re h)
    }
    let F:= viewS g t P.sym d; have h(x y:Label d)(i:Vesta g t) : e.inner (F i x) (F i y)=e.inner x y:=by
       cases i <;> rename_i i; · exact Chloe.fauna P n x y hP i
       exact Chloe.brood P n x y hP _ _ i.1.prop.1
    obtain ⟨Z,hZ,hP,hV⟩:= ports e F (quip p q g t) (bluff p q g t d) (gateL p q g t P.sym) h; refine ⟨Z,hZ,hP,fun U s hs=> ?_⟩
    have he(i x): F i x=viewS g t s d i x:=belongs ..; have h:=hV U (fun x i=>by rw [he]; exact hs x i); exact ⟨h.1,fun x hp=> h.2 x (fun i=> by rw [he]; exact hp i)⟩
end YM.Sprig
#print axioms YM.Sprig.nature
