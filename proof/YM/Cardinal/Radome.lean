import YM.Cardinal.Sund
/-! # Dealt costs split around point/reference choice. Coordinate space over C at fixed momentum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {a b t θ v:ℝ}{k d n j m:ℕ}{c:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local QCD.Kit
namespace Stamp
local instance chairB (d:ℕ): Module.Free ℂ (Label d):=Module.Free.of_divisionRing (K:=ℂ) (Label d) -- sig
noncomputable def hatch (d:ℕ): Label d≃ₗ[ℂ](Fog d→ℂ):= (Module.finBasis ℂ (Label d)).equivFun
noncomputable scoped instance normed (d:ℕ) : NormedAddCommGroup (Label d):= NormedAddCommGroup.induced _ _ _ (hatch d).injective
noncomputable scoped instance pose (d:ℕ) : NormedSpace ℂ (Label d):= .induced _ _ _ (hatch d)
noncomputable scoped instance cottage (d:ℕ) : CompleteSpace (Label d):=FiniteDimensional.complete ℂ _
open scoped YM.Massive.Poised.Plans.Stamp
-- stamp-linear
variable (s e:ℝ)
lemma liftN (p:PowerPair d) : ∃ F: Label d→L[ℂ]ℂ,∀ x:Label d, F x=Stative.fare p x.val s e:=⟨((coord p).comp ((Sieve.widths s e).comp (labels d).subtype)).toContinuousLinearMap,fun _=>rfl⟩
variable {s e}
lemma widthPoly (ht:0<s)(hv:0<e)(d:ℕ) : Injective (dimming s e d):=by
    intro i j he; apply Subtype.ext; apply (zBasis d).repr.injective; ext k; have hf: coord k (dimming s e d i).val= coord k (dimming s e d j).val:= congr_arg (fun X:Label d=>coord k X.val) he
    change coord k (Sieve.widths s e i.val)=coord k (Sieve.widths s e j.val) at hf; rw [rank_fee,rank_fee] at hf; exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast ht.ne')) (pow_ne_zero _ (by exact_mod_cast hv.ne'))) hf
variable {I:Type}
lemma shieldC (u:I→Label d)(h:Summable fun i=> wealth (u i).val s e)(ht:0<s)(hv:0<e): Summable u:=by
   let F:=Module.finBasis ℂ (Label d); obtain ⟨C,hC,H⟩:= payFrame F; let X:= LinearEquiv.ofBijective (dimming s e d) ⟨widthPoly ht hv d,(LinearMap.injective_iff_surjective).1 (widthPoly ht hv d)⟩ -- edit
   have hS : Summable (fun i=> dimming s e d (u i)):= Summable.of_norm_bounded (h.mul_left C) (fun i=> H (u i) s e)
   exact ((X.symm.toLinearMap.toContinuousLinearMap.hasSum hS.hasSum).congr_fun (fun i=>(X.symm_apply_apply (u i)).symm)).summable -- congr via convert
lemma total_wealth (u:I→Label d)(h:Summable u): wealth (∑' i,u i).val s e ≤ ∑' i, wealth (u i).val s e:=by
   choose F hF using fun i:Rings d=> liftN s e i.val; have hv : (fun k:I=> wealth (u k).val s e)=fun k=>∑ i:Rings d, ‖F i (u k)‖:=funext fun k=> sum_congr rfl fun i _=>by rw [hF]
   have hX(i): Summable fun k=> F i (u k):=( (F i).hasSum h.hasSum).summable
   rw [show (∑' i,wealth (u i).val s e)= ∑' k:I,∑ i:Rings d, ‖F i (u k)‖ from congr_arg (fun f:I→ℝ => ∑' k,f k) hv,Summable.tsum_finsetSum (f:=fun i k=> ‖F i (u k)‖) (fun i _=> (hX i).norm)] -- sig
   exact Finset.sum_le_sum fun i _=> by rw [← hF,(F i).map_tsum h]; exact norm_tsum_le_tsum_norm ((hX i).norm)
lemma moon_set (u:I→Label d)(q:Bool)(he:Summable u)(hp:∀ i,moored (u i).val q) : moored (∑' i,u i).val q:=by
    let L:= (dimming 1 (-1) d).toContinuousLinearMap; let s:=gammaQ q
    have hf(i:Label d):L i= s • i ↔ moored i.val q:=by rw [Subtype.ext_iff]; change (Sieve.widths 1 (-1) i.val)= s • i.val↔parityAct i.val=s • _; rw [Orientation.stylish i (0,∅)]
    apply (hf _).mp; rw [L.map_tsum he]; apply HasSum.tsum_eq; exact (he.hasSum.const_smul s).congr_fun fun x=> (hf _).mpr (hp _)
variable (H:TaperHol){U:Hol su} (A:Exhibit U)(b:Cover)
-- Pre-number engagements at horizon.Normalization both inputs & outputs. Types.
structure Pilot (d m k n z r:ℕ)(α β :ℝ):Prop where
    order : d ≤ m
    cap : d*d ≤ k
    weight : surface d ≤ n
    band : Fintype.card (Palette.ZBand d)<z
    footprint : Permit.used_bound (A.t d) r
    light : 1 ≤ α
    funds : 1 ≤ β
    earn (L:Side) (c:Cover)(P:BudgetPoint)(y:Label d)(V:Support L)(x:Grid L→Lat.Fields L 6)(s i:ℝ) : P.order=m → P.power=k → 0 < s → Flame x P V (wrap _ c) s n z i → ActionTest H c x y.val → wealth y.val P.threshold s ≤ α*i
    bill (c:Side)(V:Cover)(P:BudgetPoint)(s:ℝ)(y:Label d) : P.order=m → P.power=k→ 2*(r+1)< c.val →0<s → Flame (graphs (c:=c) d A V y) P (pot (r+1) c V) (wrap c V) s n z (β*wealth y.val P.threshold s)
    tested (c:Side)(V:Cover)(q:Label d) : 30*(r+1) ≤ c.val → ActionTest H V (graphs (c:=c) d A V q) q.val
variable (d)
lemma services (m k n z :ℕ)(ht:d ≤ m)(hk:d*d ≤ k)(hz:Fintype.card (Palette.ZBand d)<z)(hP:surface d≤n) : ∃ (r:ℕ) (α β:ℝ),Pilot H A d m k n z r α β:=by
    let F:=Module.finBasis ℂ (Label d); -- `Permit.used_bound` growth.Ex.
    obtain ⟨p,hp⟩:= (Permit.eventual (A.t d)).exists; let r:=p+2; have he:Permit.used_bound (A.t d) r:=by
       intro i hi a; exact (hp _ hi a).trans (by unfold r; omega)
    choose C hC hU using fun i:Rings d=> Stative.chapter d m n k i hP ht hk F
    obtain ⟨X,hX,hV⟩:= Facets.massy U A F he k m n z; obtain ⟨M,hM,hW⟩:= payFrame F
    let B:=∑ i,C i; refine ⟨r,max 1 B,max 1 (X*M),⟨ht,hk,hP,hz,he,le_max_left ..,le_max_left ..,fun L c P y V x s i he hp hv hF hd=>?_,fun c V P s y he hp hh hv=>?_, fun c V q hp'=> Orientation.graph_obs (n:=0) d H A V _ (by -- infer k unresolved
           intro i hi a; have he:= hp i hi a; omega)⟩⟩
    · apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) hF.sight.travels); unfold wealth B; rw [Finset.sum_mul]; exact Finset.sum_le_sum fun j _=> hU j H L x c V P z s i hp he hF hz hv _ ((label_law _).1 y.property).1 hd
    apply leFlame (hV V P c hp he hh _ hv y); exact (mul_le_mul_of_nonneg_left (hW ..) hX).trans ((mul_assoc ..|>.symm.le).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (wealth_ge ..)))
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.services
