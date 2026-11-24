import YM.Vern.Lands
set_option maxHeartbeats 540000
set_option autoImplicit false
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp Heron Iceberg Lobo
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {φ:ℕ→ℕ}
variable (hf:Foil P K T)(HQ:K.Harmony P φ)(E:Canopy P φ K)(X:Lanterns T E)
variable {d:ℕ}(V:Face→K.W)(A:Persona T V) (J:Axle K (fun a b=>V (a,b))) (U:Vane J)(hd:8≤d)
include hf HQ U A
lemma pinnacle (a b c:Axis)(h:a≠c)(h':b≠c)(r:ℝ)(hr:0<r) : Tide.Leans (entryQ hf HQ c r hr d) (tapeJ K V J hd (Ortho.plane a b)):=fun x y=> skewJ HQ.h hf V A J U a b c h h' x y r hr
variable (f:ℕ→ℕ)
set_option quotPrecheck false
lemma wraps (k:ℕ) (i:Tri): Tide.Leans (haloZ hf HQ E X d k) (foldQ V E X A J hd (Omega i) k):=by
     let r:=(E.B k).r; let T':= entryQ hf HQ timeAxis r (E.B k).realH d; let F:=X.frame k d; let c:ℝ:= (peakΩ V A.tense E X k)⁻¹; let q:= tapeJ K V J hd (Omega i); have ht:T'.Leans q:= pinnacle hf HQ V A J U hd _ _ timeAxis (fun h=>Fin.castSucc_ne_last _ h) (fun h=>Fin.castSucc_ne_last _ h) _ _
     intro x y; change T'.knot (F ((c:ℂ) • F.symm (q (F x)))) (F y) = -(T'.knot (F x) (F ((c:ℂ) • F.symm (q (F y))))); rw [map_smul,map_smul,F.apply_symm_apply,F.apply_symm_apply,T'.seals,T'.sep, Complex.star_def, Complex.conj_ofReal,ht,mul_neg]
variable (Z:Lobo.Tri)(Q0:Module.End ℂ (Free.Symbol d))(hF:Tendsto f atTop atTop)(H:∀ v:Free.Symbol d,Tendsto (fun i=> foldQ V E X A J hd (Omega Z) (f i) v) atTop (𝓝 (Q0 v)))
include H hF
lemma apex : (GStar hf HQ E X d).Leans Q0:=by
     intro v x; let Uz(i):=haloZ hf HQ E X d (f i); let G:= GStar hf HQ E X d; let p(x y:Free.Symbol d): Tendsto (fun i=>(Uz i).knot x y) atTop (𝓝 (G.knot x y)) := (paths hf HQ E X y x).comp hF
     apply tendsto_nhds_unique (knot_seat G Uz p (Q0 v) x _ (fun _=>x) (H v) tendsto_const_nhds); apply ((knot_seat G Uz p v (Q0 x) (fun _=>v) _ tendsto_const_nhds (H x)).neg).congr'; refine Eventually.of_forall fun k=> ?_ ; exact (wraps hf HQ E X V A J U hd (f k) Z v x).symm -- U naming!
lemma blaze (hx:Q0≠0):∃ r:ℝ,0<r∧ Tendsto (fun i=>peakΩ V A.tense E X (f i)) atTop (𝓝 r):=by
     let F:=entryQ hf HQ timeAxis 1 zero_lt_one d; let D:=GStar hf HQ E X d; exact meter F D _ Q0 _ (fun i=>viable V E X (f i) A) (fun i=>X.frame (f i) d) (pinnacle hf HQ V A J U hd _ _ timeAxis (fun h=>Fin.castSucc_ne_last _ h) (fun h=>Fin.castSucc_ne_last _ h) 1 zero_lt_one) (apex hf HQ E X V A J U hd f Z Q0 hF H) hx (fun v=>by
             let p:= tapeJ K V J hd (Omega Z); simp_rw[ ← Complex.ofReal_inv]; exact H v)
end YM.Vern
#print axioms YM.Vern.blaze
