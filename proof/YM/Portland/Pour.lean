import YM.Portland.Count
import YM.Mural.Sura
import YM.VMarker.Cents
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat
open PaletteT Ribbon
variable {c f:Side}{j k N:ℕ}
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist Kites Creek Cove
open NormedSpace Grass.Ovule
variable {I E:Type}(Z:PrintR f N Rank I E)(D:DeckV f N)(i:Rank)
set_option quotPrecheck false
local notation "QO"=>D.O
local notation "E'"=> Z.regE (.some i)
local notation "R"=>(E').rope (D.O).threshold 1
local notation "F'"=> Z.regK (.some i)
local notation "D1"=>D.E 1
local notation "F"=>Keys f N
local notation "Kt"=> rootR (Spine Unit) (Keys f N)
local notation "WE"=> pluck (Keys f N) sD
local notation "eq0"=>D.density (1:Grid f)
lemma oneD (D:DeckV f N): D.density (1:Grid f)=exp (Cove.light _ (D.E 1)):=by
    unfold DeckV.density; rw [High.PrismT.bank D.K _ D.O.threshold (UVNext.CouplingReset.flags_one ..),mul_one]; exact light_exp ..
variable (x y:Site f)(P:Support f)(U:TokenP)
variable (hP:Z.Fides (fun _=>x) P D.O (fieldD x y))(hV: Z.Levy D.O U.t U.f U.e U.k U.v U.w U.s)
include hP
lemma caste : Pillars E' (fun _=> x) qT P:= (hP.tinted (fun _=>1)).blocking _
local notation "T"=>E'
lemma tribute (j:I):Polite qT {()} ((T).mist D.O.threshold j 1):=by
    let S:= T; have h:=caste Z D i x y P hP; have hz:(T).z j= {()}:=by ext i; cases i; obtain ⟨u,hu⟩:= h.stays j; cases u; simp [hu]
    rw [←hz]; have hx: Polite qT _ ((T).mark j 1):=(h.stage j 1).1; unfold Reel.mist masked Set.indicator; split; exact hx; exact polite_nil .. 
lemma flagless : Film.reports N F' D.K (D.O).threshold 1=1:=by
    let Y:=Film.addressSets N (Z.regK (.some i)) D.K; unfold Film.reports; rw [UVNext.CouplingReset.flags_one, tsum_eq_single ∅]
    · rw [Plate.roof,if_pos ?_,prod_empty]; exact ⟨fun i hi=>(notMem_empty i hi).elim,biUnion_empty⟩
    intro j h; unfold Plate.roof; split; next he=> obtain ⟨s,hs⟩:=nonempty_iff_ne_empty.mpr h; have hx:= (Y s).alive; obtain ⟨t,ht⟩:=hx; have hv':t∈ j.biUnion (fun x=>(Y x).inv):=mem_biUnion.mpr ⟨s,hs,ht⟩; rw [show j.biUnion _=_ from he.2] at hv'; simpa using hv'
    next=>rfl
lemma ink : D.emblem Z (some i) sD 1 =eq0* WE R:=by
    have hp:Polite qT {()} R:= polite_tsum fun j=> tribute Z D i x y P hP j
    have hv : NormedSpace.exp R=1+R:=by
        apply Subtype.ext; change Cove.light _ (exp R)= (1: Alg _)+(R).val; rw [light_exp]; exact radius_two _ (congr_arg Subtype.val (hp.nilpotent hp (by simp)))
    unfold DeckV.emblem relativeE; rw [exp_add,flagless Z D i x y P hP, mul_one, ← NormedSpace.map_exp Kt ((Kt).toLinearMap.toContinuousLinearMap.continuous),hv,freights,map_add]
    have hh: pluck (Keys f N) sD (1:Patio (Keys f N⊕Spine Unit))=0:= (polite_empty_one (A:=Keys f N) qT).spectral _ (by rw [←fullB,burst_absent]; exact (burstPos _ (singleton_nonempty ())).ne_empty) -- infer
    rw [hh,zero_add,oneD]; exact congr_arg (· * (WE R)) (light_exp (D.E 1))
omit hP
lemma brightness : Plus (WE R):=by
    have hh:= Ribbon.serene sD (bright R) -- arg check
    rw[← fullB, Ribbon.flavor] at hh; rw[←fullB]; exact hh
open Push.AbsoluteSums
include hP hV
lemma hpBoast (h:x∈P)(ht:1 ≤ U.t)(hp:1≤U.f)(hα:0≤U.e)(hβ:0≤U.k)(hγ:1≤U.w) : repay univ U.t 4 (fun _=>U.f) (WE R) ≤ U.v:=by
      let R':=(T).mist D.O.threshold; let F0(j:I):= R' j (1:Grid f); let B0:=U.v
      have hx:HasSum F0 R:=(Summable.of_norm ((billP Z (1:Grid f) D.O U.f U.t U.e U.k U.v U.w U.s hV hp hγ ht hα hβ (.some i)).1)).hasSum
      obtain ⟨g,hG,he⟩:=hV.budget (some i)
      have hi : SumBudget g B0:=budget_mono (he x) (fun i=>(repay_pos ..).trans (hG i 1)) fun j=>by
         rw [if_pos (show x∈ Z.mrR j from (caste Z D i _ _ P hP).boast j h)]; exact le_mul_of_one_le_right ((repay_pos ..).trans (hG j 1)) (Real.one_le_exp (mul_nonneg hα (Nat.cast_nonneg _)))
      have hv(j:I): repay univ U.t 4 (fun _=>U.f) (WE (F0 j))≤g j:=by rw [←fullB]; exact ((attachedM f N Unit U.f U.t 4 (zero_lt_one.trans_le hp) _ (tribute Z D i x y P hP j)).symm.le.trans (hG j 1))
      have hs: HasSum (fun j:I=> WE (F0 j)) (WE R):=hx.map WE (WE).continuous
      exact le_of_tendsto' ((repContinu univ U.t 4 (fun _:Keys f N=>U.f)).continuousAt.tendsto.comp hs) (fun s: Finset I=> le_trans (repay_sum univ U.t 4 (fun _=>U.f) s (fun j=>WE (F0 j))) ((sum_le_sum fun j _=>hv j).trans (budget_sum hi s)))
end YM.QCD.Comet
#print axioms YM.QCD.Comet.hpBoast
#print axioms YM.QCD.Comet.ink
