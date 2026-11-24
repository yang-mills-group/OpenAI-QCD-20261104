import YM.Profiles.Standards
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {I J E D' :Type}[Fintype I][Fintype J]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j:ℕ}
namespace Publicity
open NormedSpace Quills ProfileL
variable (S:Flight m d)(h₀:f.val=c.val*S.L.val)(K: KernelChoices)(β w:ℝ)
variable (N:ℕ)(q:I→Bool)(p:J→Bool)(P:Set (Finset J))(P₀:Set (Finset I))(r:I→J→Prop)(g:I→J→ℝ)(F:Grid f→ Patio (Keys f N⊕Spine I))(Y:Grid c→ Patio (Keys c N⊕Spine J)){z:ℂ}
variable (hX:Pledge q p r P P₀)(hp:Publicity q S h₀ K β w F P₀ r P p g z Y)
local notation "T"=> Massive.transfer S K h₀ β w
local notation "A"=> Keys c N
local notation "A⁺"=> Keys f N
include hp hX
lemma coasts (s:Fin n→ J)(hx:Injective s)(hv:crest s∈P): z • (numbered p A s ∘ Y)= ∑ u:Queue r s, beans r g s u • T (numbered q A⁺ (attends r s u) ∘ F):=by
    let Z:=crest s; let p':=numbered p A s; let q':=shutter (Keys c N) Z; let u:= Sample.flame A q p (findV r Z) g; obtain ⟨G,hG,hΦ,hW⟩:=hp.tracks
    have he:∀ x: Patio (A⊕Spine J), p' (q' x)=p' x:=by
        intro x; change signG p s • pluck A (burst p Z) (shutter A Z x)= signG p s • pluck A (burst p Z) x; rw [Cupola.shutter,Cupola.pulse,Cupola.sensed,show ∏ i∈Z,(↑(if i∈Z then (1:ℝ) else (0:ℝ)):ℂ)=1 from (prod_eq_one (fun i hi=>by simp [hi])),one_smul] -- cast? expression cast if → ℂ
    let v(b:Queue r s):= attends r s b
    have h(v':Queue r s): T (numbered q A⁺ (v v') ∘ F)= z • (numbered q A (v v')∘ G):=by
        let s':= v v'; let e:= crest s'; let φ:= pluck A⁺ (burst q e); let D:= T (φ ∘ F); have hg:D=z • (pluck A (burst q e) ∘ G):=funext (hΦ _ (hX.was _ _ (usher q p P P₀ r hX s v' hv hx))); change T (signG q s' • (φ ∘ F))= z • (signG q s' • (pluck A (burst q e) ∘ G)); unfold D at hg; rw [Rails.scalar_transfer,hg,smul_comm]
    funext V; have ht:= he (Y V); rw [Pi.smul_apply,show (numbered p A s ∘ Y) V=p' (q' (Y V)) from ht.symm,← show u (G V)= q' (Y V) from hW _ hv _,show p' (u (G V))=_ from billSlide A q p P P₀ r g hX s hv hx _ (hG V),Finset.smul_sum, Finset.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_; rw [show T _=_ from h i]; exact smul_comm ..
lemma zeros : T (pluck A⁺ ∅ ∘ F)=z • (pluck A ∅ ∘ Y):=by
    let s: Fin 0→J:=fun i=> Fin.elim0 i; have hx: crest s=∅:=by simp [Quills.crest]
    have v:=(coasts S h₀ K β w N q p P P₀ r g F Y hX hp s (fun _ _ _=>Subsingleton.elim ..) (hx.symm ▸ hX.mast.empty)); haveI : Unique (Queue r s):= by unfold Queue; infer_instance
    have hT':v=v:=rfl; clear hT'; rw [Fintype.sum_unique,beans,Fin.prod_univ_zero,one_smul] at v
    have h : numbered q A⁺ (attends r s default)=pluck A⁺ ∅:=ContinuousLinearMap.ext (emptyN (A⁺) q _); have h': numbered p A s=pluck A ∅:=ContinuousLinearMap.ext (emptyN A p _); rw [h,h'] at v; exact v.symm
lemma single (i:J)(h:{i}∈P): z • (pluck A (burst p {i}) ∘ Y)= ∑ v:To r i, (↑(g v.val i):ℂ) • T (pluck A⁺ (burst q ({v.val}:Finset I)) ∘ F):=by
   let s: Fin 1→J:=fun _=>i; have he:crest s={i}:=by simp [Quills.crest,s]
   have hv :numbered p A s=pluck A (burst p {i}):=ContinuousLinearMap.ext (singleN A p s)
   rw [← hv,coasts S h₀ K β w N q p P P₀ r g F Y hX hp _ (fun _ _ _=>Subsingleton.elim ..) (he.symm ▸ h)]; let H:= Equiv.piUnique (fun j:Fin 1=> To r (s j)); refine Fintype.sum_equiv H _ _ ?_; intro u; let v:=attends r s u; have heq:v 0=(H u).val:= congr_arg (fun i=> (u i).val) (Subsingleton.elim ..); rw [beans,Fin.prod_univ_one]; have hQ:numbered q A⁺ v=pluck A⁺ (burst q {v 0}):= ContinuousLinearMap.ext (singleN (A⁺) q v); change (↑(g (v 0) (s 0)):ℂ) • T (numbered q A⁺ v ∘ F)=_; rw [hQ,heq]
end Publicity
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Publicity.coasts
#print axioms YM.MassiveQCD.Sample.Publicity.zeros
