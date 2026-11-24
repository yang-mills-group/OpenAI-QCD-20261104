import YM.Vern.Muzzle
import YM.Vern.Joe
set_option autoImplicit false
set_option maxHeartbeats 690000
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat QCD.Grass
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp Heron Iceberg Lobo NativeV
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K}{d:ℕ}
variable {φ:ℕ→ℕ}(hf:Foil P K T)(HQ:K.Harmony P φ)(E:Canopy P φ K)(X:Lanterns T E)
variable (V:Axis× Axis→ K.W)(hV: Persona T V)(J:Axle K (fun a b=>V (a,b))) (B:Vane J)
variable (r:ℝ)(hr:0<r)(s:ℝ)
set_option quotPrecheck false
local notation "X₄"=> ↥(seedP T 8)
local notation "X₅"=> ↥(seedP T 10)
local notation "Xr" i:arg => (↑s:ℂ) • jRoad hf HQ V hV J (Omega i) (Nat.le_refl 8)
local notation "Xt" i:arg => (↑s:ℂ) • jRoad hf HQ V hV J (Omega i) (show 8≤10 from by decide)
local notation "Tz" => Jcost hf HQ r hr 10
include hf HQ
noncomputable def scalarD (T:Pollens P K)(d:ℕ): ↥(seedP T d) →ₗ[ℂ]K.W:= (K.level d).subtype ∘ₗ (seedP T d).subtype
lemma toe : Injective (scalarD T d):= fun x y he=>Subtype.ext (Subtype.ext he)
noncomputable def lying (a:Axis) : (seedP T 8) →ₗ[ℂ] (seedP T 10) :=by
    let D: ↥(K.level 8)→ₗ[ℂ]↥(K.level 10):=(K.arc a).restrict (fun v hv=> HQ.h.graded a 8 v hv); refine D.restrict (fun x hx=> ?_); let v:=x.val; have hv:v∈ safeV T:=hx
    exact ⟨(inward hf HQ.h T.parity v hf.parity a).trans (congr_arg _ hv.1),fun u=>(inward hf HQ.h (T.flavor u) v (fun n x hx=>hf.flavor n x hx u) a).trans (congr_arg _ (hv.2 u))⟩
include B hV
noncomputable def metal : Medal ↥(seedP T 10):=by
     let F:=Tz; refine {T:= F,J:=fun i:Tri=> (Xt i),K:=fun i=>(shipP HQ.h i 10).toLinearMap,unit:=fun i x y=>?_,skew:=fun i x y=> Eq.trans (pitG hf HQ V hV J B r hr s (show 8≤10 from by decide) i x y) ?_}
     · change turf timeAxis r (T:=T) (shipP HQ.h i 10 x).val.val (shipP HQ.h i 10 y).val.val=_; rw [sails,sails]; exact tips hf HQ _ _ hr _ _ x.property.1
     exact map_neg (F.zz x) _
local notation "R"=> metal hf HQ V hV J B r hr s
lemma Lutz (i:Tri)(a b:Axis)(hx:a=timeAxis∨b=timeAxis): (Omega i).val a b=0:=by
       fin_cases i <;> cases hx with | inl h=>rw[h]; fin_cases b<;>simp +decide [timeAxis,Omega,Ortho.plane,Matrix.single_apply] | inr h=>rw[h]; fin_cases a<;>simp +decide [timeAxis,Omega,Ortho.plane,Matrix.single_apply]
lemma sparkX (x:X₄)(i:Tri)(a:Axis): scalarD T 10 (((Xt i) (lying hf HQ a x))- lying hf HQ a ((Xr i) x))=(s:ℂ) • ∑ j:Axis, (↑((Omega i).val j a):ℂ) • B.edge j x.val.val :=by
       have hk:= Vane.sparks hf HQ.h J x.val.val a (Omega i) B; rw [← hk]; -- check
       change (↑s:ℂ) • _ - K.arc a ((↑s:ℂ) • _) = _; rw [map_smul,smul_sub]; rfl
noncomputable def dayV :Drift (metal hf HQ V hV J B r hr s) X₄:=by
       refine {d:=lying hf HQ,J:=fun i=> Xr i,K:=fun i=>(shipP HQ.h i 8).toLinearMap, geo:=fun i a x=>?_,awe:=fun i x=>?_,twist:=fun i x=>?_,torque:=fun i j x=>?_}
       · apply toe hf HQ; change _=(charI i a:ℂ) • K.arc (lieu (roof i a)) (shipP HQ.h i 8 x).val.val; rw[sails]; change (shipP HQ.h i 10 (lying hf HQ (lieu a) x)).val.val=_; rw [sails]; change T.spin _ (K.arc _ _)=_; rw [pith hf HQ.h _ _ _ _ (fL i), viaC, coar]; rfl
       · apply toe hf HQ; change (shipP HQ.h i 10 (lying hf HQ timeAxis x)).val.val= K.arc timeAxis (shipP HQ.h i 8 x).val.val; rw [sails,sails]; change T.spin _ (K.arc _ _)=_; rw [pith hf HQ.h _ _ _ _ (fL i), (coreTime i).1,(coreTime i).2,Complex.ofReal_one,one_smul]; rfl
       · apply sub_eq_zero.mp; apply toe hf HQ; rw [show (R).J i=Xt i from rfl,map_zero, show scalarD T 10 _= _ from sparkX hf HQ V hV J B s x i timeAxis]; simp_rw [show ∀ j:Axis,(Omega i).val j timeAxis=0 from fun j=> Lutz hf HQ V hV J B i j _ (Or.inr rfl), Complex.ofReal_zero,zero_smul,Finset.sum_const_zero, smul_zero] -- Lutz arity
       · apply toe hf HQ; rw[show (R).J i=Xt i from rfl, show (R).J j=Xt j from rfl,map_zero,map_add,show scalarD T 10 _= _ from sparkX hf HQ V hV J B s x i (lieu j), show scalarD T 10 _=_ from sparkX hf HQ V hV J B s x j (lieu i), ← smul_add,← Finset.sum_add_distrib]; apply smul_eq_zero.mpr; right; apply Finset.sum_eq_zero; intro k _; rcases Fin.eq_castSucc_or_eq_last k with ⟨z,h⟩|h
         · rw[h]; change waveT i j z • _+ waveT j i z • _=0; rw [eOG,neg_smul,neg_add_cancel]
         rw [h]; change (↑((Omega i).val timeAxis _):ℂ) • _+(↑((Omega j).val timeAxis _):ℂ) • _=0; rw [Lutz hf HQ V hV J B i timeAxis _ (Or.inl rfl), Lutz hf HQ V hV J B j timeAxis _ (Or.inl rfl)]; simp; -- fix
end YM.Vern
#print axioms YM.Vern.dayV
#print axioms YM.Vern.metal
