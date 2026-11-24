import YM.Avian.Onyx
import YM.Avian.Skein
/-! Finite rank of aligned charge Neutral. No choice chart assumes proper rotations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Onyx
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Tawny Tawny.Cast Tawny.Cast.TableT Tawny.Cast.Rays Perla Fore Perla.BrickM Zinc Carnal
open Pane BendR UV.Free KeysP Clifford
open YM.Sprig Tarn Tarn.Choir Pollens
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}(T:Pollens P Q) {I:Type}[Fintype I](J:Nest I)(d:ℕ)
variable (V:I→Averaging)
local notation "B"=> Plain J d
noncomputable def polls (Q:Choir): Plain J d→ₗ[ℂ] (I→Q.W):= grab d J fun i=> Q.focus (V i) d
noncomputable def prize : Plain J d→ₗ[ℂ] (I→UV.Free.Symbol d) := grab d J (Y:=UV.Free.Symbol d) fun _=> projection -- instance
variable (x:UV.Free.Symbol d≃ₗ[ℂ]↥(Q.level d))(hx: YM.Sprig.Prose x T)
def Veer (J:Nest I)(V:I→Averaging):Prop:=∀ i k, Averaging.permute i (V k)= V (J.Q i k)
local notation "f" u:arg i:arg => Q.focus u d i
-- orientation in polls swap also need V t(k)= V k
lemma calmP (h:Veer J V)(hv:∀ i,V (J.t i)=V i): PulseT J d (fun i=> Q.focus (V i) d) (lion T J) P.sym:=by
     constructor; intro i v j; let G(i):= Q.focus (V i) d; rcases i with a|j'
     · exact (T.f ..).symm
     rcases j' with p | b
     · obtain ⟨⟨p,s⟩,hp⟩:=p; let S:= J.Q s; let W:= S.symm j; let k:ℂ:= J.c s W; change G j (k • (P.sym.pin d p (v W)))= k • T.spin p (G W (v W)); rw[map_smul]; apply congr_arg; unfold G; rw [T.w _ s hp,h]; change _=Q.focus (V (S (S.symm j))) d _; rw[S.apply_symm_apply]
     fin_cases b
     · exact (T.p ..).symm
     · exact (T.c ..).symm
     change Q.focus (V j) d (v (J.t j))= Q.focus (V (J.t j)) d _; rw[hv]
noncomputable def proves (x:UV.Free.Symbol d≃ₗ[ℂ] ↥(Q.level d)):Label d→ₗ[ℂ] Q.W:= (Q.level d).subtype ∘ₗ x.toLinearMap ∘ₗ projection
include hx
lemma proven : PulseT J d (fun _=> proves d x) (lion T J) P.sym:=by
     constructor; intro i v j; let L:= proves _ x; rcases i with a|j'
     · exact (hx.turns (v j) a).symm
     rcases j' with p | b
     · obtain ⟨⟨p,s⟩,hp⟩:=p; let S:= J.Q s; let W:= S.symm j; let k:ℂ:= J.c s W; change L (k • (P.sym.pin d p (v W)))= k • T.spin p (L (v W)); rw[map_smul]; apply congr_arg; exact (hx.rotates _ p s hp).symm
     fin_cases b; exact (hx.spins (v j)).symm; exact (hx.jumps (v j)).symm; rfl
lemma reach_point {t : (I→Label d)→ₗ[ℂ] (I→Label d)}(ht:Tackle d J t)(h:Veer J V)(hv:∀ i,V (J.t i)=V i)(hD:Q.Domestic): (polls J d V Q).range=(grab d J (fun i=> proves d x)).range :=by
    apply Submodule.ext; intro i; change i∈(grab d _ _).range↔_; rw[portrait d J (calmP T J d V h hv) _ ht, portrait d J (proven T J d x hx) _ ht]; apply and_congr_right; intro _; suffices hh:∀ i,(Q.focus (V i) d).range=(proves d x).range by simp_rw [hh]
    intro i; rw[hD.tops]; apply Eq.symm; apply Submodule.ext; intro z; constructor; · rintro ⟨s,rfl⟩; exact (x (projection s)).property
    intro h; obtain ⟨t,ht⟩:=x.surjective ⟨_,h⟩; obtain ⟨s,rfl⟩:= UV.Free.onto t; exact ⟨s,congr_arg Subtype.val ht⟩
-- ratio dimension preserves with Prose.
variable (k:I)(n:Side)(hD:Q.Domestic)(hP:P.System)(hg:Injective (P.candidate d n 0))(hh:Veer J V)(hr:∀ i,V (J.t i)=V i)
include hg hD hP hh hr
lemma point_rank : Module.finrank ℂ (polls J d V Q).range=Module.finrank ℂ (prize J d).range:=by
     obtain ⟨t,ht⟩:= paddle d J n hP hg; rw[reach_point T J d V x hx ht hh hr hD]; let Z:(I→ UV.Free.Symbol d)→ₗ[ℂ] (I→Q.W):= LinearMap.pi fun i:I=> (Q.level d).subtype ∘ₗ x.toLinearMap ∘ₗ LinearMap.proj i; rw [show grab d J (fun i=>proves d x)= Z ∘ₗ (prize J d) from LinearMap.ext fun i=> rfl, LinearMap.range_comp]; have he:Injective Z:=by intro i j he; funext k; have hp: ((x (i k)).val)= (x (j k)).val:=congr_fun he k; exact x.injective (Subtype.ext hp)
     exact (Submodule.equivMapOfInjective Z he _).finrank_eq.symm
end YM.Massive.Patria.Gall.Onyx
#print axioms YM.Massive.Patria.Gall.Onyx.point_rank
