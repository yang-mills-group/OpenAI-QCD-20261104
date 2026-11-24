import YM.Mural.Sym
import YM.QCD.Villa.Music
/-! # Integration of company array in a gauge motion. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.PaletteT
open QCD QCD.Grass QCD.Creek Cupola QCD.Cove QCD.Sway QCD.Sway.OrbitG Function Finset Filter MeasureTheory NormedSpace
open Plate Stitch Tablet Ribbon Lattice Wilson Lat
open scoped BigOperators Topology Classical ContDiff
variable {P X Z A:Type*}{I:Type} [Fintype I]
local notation "Ip"=> Option I
variable {D:Type}[Fintype D]
local notation "K"=>Patio D
variable (F:Submodule ℂ (Option I→Patio D)) (f:Ip→ X→ K)
section integral
variable [MeasurableSpace X] {μ:Measure X} (p: Option I→ X→ Patio D)
include F
lemma entered [IsProbabilityMeasure μ](hp:∀ i,Integrable (p i) μ)(h:∀ x,(fun i=> p i x)∈F): (fun i=>∫ x, p i x ∂μ)∈ F:=by
    let F':= F.restrictScalars ℝ; let T (x:X):= fun i=> p i x; have hm : Integrable T μ:=by
       exact integrable_pi_iff.mpr hp
    have hF:=F.closed_of_finiteDimensional
    have hg: (∫ x,T x ∂μ)∈ F:= F'.convex.integral_mem hF (Eventually.of_forall h) hm
    convert hg using 1; funext i; exact (eval_integral (f:=T) hp i).symm
omit F
lemma seen {D' :Type*}[MeasurableSpace D']{κ:Measure D'}(r:D'→ X)(u:Option I→ D'→Patio D) (T:Delta I)(H: Patio D→ₐ[ℂ] Patio D) (h:MeasurePreserving r κ μ)(hp:∀ i,Measurable (p i))(ht:∀ i, Integrable (p i) μ)(hs:∀ i, Integrable (u i) κ)(hh:∀ v,Binds T H (fun i=> p i (r v)) (fun i=>u i v)) : Binds T H (fun i=> ∫ x,p i x ∂μ) (fun i=> ∫ x,u i x ∂κ):=by
    intro i; let V v:= ∑ j:Ip,T i j • u j v; have ht' : Integrable V κ:= by apply integrable_finsetSum; intro j _; exact (hs j).smul (T i j)
    have hX : H (∫ x,p i x ∂μ)= ∫ x,V x ∂κ := by
       let A:= H.toLinearMap.toContinuousLinearMap.restrictScalars ℝ
       change A _=_
       rw [← A.integral_comp_comm (ht _)] -- orientation edit
       -- pull.S.P
       apply YM.QCD.Beam.concrete; intro l
       rw [← l.integral_comp_comm (A.integrable_comp (ht i)),← l.integral_comp_comm ht',← YM.ConnectedActivityE6.Pond.reception h (fun x=>l (A (p i x))) (l.measurable.comp (A.measurable.comp (hp _)))]
       exact integral_congr_ae (Eventually.of_forall fun v=> congr_arg l (hh v i))
    apply hX.trans
    unfold V aggregate; rw [integral_finsetSum]; simp_rw [integral_smul]; exact fun j _=> (hs j).smul (T i j)
end integral
lemma shines (p:X→Option I→ Patio D) (S:Finset X)(h:∀ i∈S,p i∈ F) : (fun i=> ∑ j∈S,p j i)∈ F:=by
    have hV:= Submodule.sum_mem F h; convert! hV using 1; ext i; rw [Finset.sum_apply]
lemma gatheredX (p:X→Option I→ Patio D) (S: Finset X)(h:∀ i∈S,p i∈F)(he:(fun _=>1)∈F)(ht:∀ x∈F,∀ y∈F,x*y∈F): (fun i=>∏ j∈S,p j i)∈F:=by
    induction S using Finset.induction_on with
    | empty=> simpa using he
    | insert i S hi ih=> simp_rw [prod_insert hi]; exact ht _ (h i (mem_insert_self ..)) _ (ih (fun j hj=>h j (mem_insert_of_mem hj))) -- defeq
lemma entrance (p:X→Option I→ Patio D)(h:∀ j,p j∈F)(hs:∀ j,Summable fun i=>p i j): (fun i=>∑' j,p j i)∈F:=by
    have hh: HasSum p (fun i=> ∑' j,p j i):=by
       apply tendsto_pi_nhds.mpr; intro i; simp_rw [Finset.sum_apply]; exact (hs _).hasSum
    apply F.closed_of_finiteDimensional.mem_of_tendsto hh; exact Eventually.of_forall fun i:Finset X=> Submodule.sum_mem F (fun j _=>h _)
lemma toExp (p: Option I→Patio D)(h:p∈F)(hp:∀ x∈F,∀ y∈F,x*y∈F)(he:(fun _=>1)∈ F) : (fun i=> exp (p i))∈ F:=by
    let f(n:ℕ):= fun i=> ((n.factorial:ℂ)⁻¹) • (p i)^n; have hh(n:ℕ):(fun i=>(p i)^n)∈ F:=by induction n with
                    | zero=> simp only [pow_zero]; exact he
                    | succ n ih=>simp_rw [pow_succ]; exact hp _ ih _ h
    have ht i: HasSum (fun n=> f n i) (exp (p i)):=exp_series_hasSum_exp' _
    have hV n: f n∈F:= F.smul_mem _ (hh n); have hx:= entrance F f hV (fun i=> (ht i).summable); convert hx using 1; funext i; exact (ht _).tsum_eq.symm
end YM.MassiveQCD.PaletteT
#print axioms YM.MassiveQCD.PaletteT.entered
#print axioms YM.MassiveQCD.PaletteT.toExp
#print axioms YM.MassiveQCD.PaletteT.seen
