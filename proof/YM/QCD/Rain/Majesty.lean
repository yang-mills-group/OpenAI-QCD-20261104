import YM.QCD.Rain.Zen
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rain
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {c L:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar Acre Rails Pressure ConnectedActivityE6 Cost Free Pine
open Raft ParcelR PhysicalNext.Repeat Next.Free Acre Rails Precision ConnectedActivityE6
variable {T':Teller su}{V':ConnectedActivityE6.Target su T'}{O:Patch}{Ω:ParcelR}{Y U W V: ℕ→ℝ}{X:ℕ→SunR Ω}{P':ℕ→BudgetPoint}{Q: Policy V' T'.top N}{t:ℕ}{f:Side} {Λ:ℝ}
-- open Branch 
lemma dawning {Z:Pixel c N}(X:Cut c N)(h:X.t=0) (he:∀ A,Cove.light _ (Z A)=primalD c N X.β X.m A) (hp:Even N): Continuous Z∧realP Z∧ Cvol Z=X.partitionR:=by
    have hU:X.ferm=fun U=> copies N (bareD 0 U X.m):=by unfold Cut.ferm; rw [h]
    have ht V:cBer Z V=X.rate 1 V:=by
         change ber _ (Cove.light _ (Z V))=_; rw [he]; unfold primalD; rw [show _ • _ = (↑(bare X.β V):ℂ) • gauss (X.ferm V) from ?_,map_smul]; simp only [Cut.rate,mul_one,Cut.insertD_apply,smul_eq_mul]
         rw [hU]; rfl
    have hx(V):Z V=levit c N (primalD _ _ X.β X.m V):= by rw [←he,callH]
    refine ⟨?_,fun A=> ?_,?_⟩
    · rw [funext hx]; unfold primalD; have hh:Continuous fun A:Grid c=> gauss (copies N (bareD 0 A X.m)):= by fun_prop
      fun_prop
    · rw [ht, ← Cut.scaled_real,Complex.ofReal_re]; exact ⟨rfl, X.real_nn (Or.inr hp) A⟩
    unfold Cvol; simp_rw [ht]; exact X.raw_one
lemma sunlight (S:Flight j j)(h:f.val=c.val*S.L.val)(K:KernelChoices)(p t:ℝ)(X:Pixel f N)(Y:Pixel c N)(he:0<t)(hK:S.patch.Branches K su)(hx:Continuous X)(hp:∀ i,advance S K h X p i=gBody _ t (Y i))(hX:realP X): realP Y:=by
     intro i; have hz : ber _ (advance S K h X p i)= (gain t⁻¹ c N:ℂ)*cBer Y i:=by rw [hp]; exact crestP ..
     obtain ⟨hr,hh⟩:= assets S h X K hK hx p i hX; let G:=gain t⁻¹ c N; have he':0<G:=pow_pos (inv_pos.mpr he) _
     rw [hz, Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr hh
     exact ⟨mul_left_cancel₀ (show (G:ℂ) ≠0 from by exact_mod_cast he'.ne') (hr.trans (Complex.ofReal_mul ..)), nonneg_of_mul_nonneg_right hh he'⟩
section ray
open Sparks
variable (B:SparkMesh){S':ℕ→SparkMesh} (g:PulseRide T'.bind T'.top.clip O a d S' k)(b:Flavor N) (A0:∀ j:ℕ,Pixel (towerQ O B k j n) N) (H: Stargate T' B b g P' X Y ε u η r z n V U W A0)
variable (hB:O.Branches T'.bind su)(hN:Even N)
include H hB hN
lemma firms (j:ℕ)(h:j ≤ k): Continuous (A0 j)∧realP (A0 j):=by
     induction j with
     | zero=>
         let K:= (⟨V 0,0,U 0⟩: Cut (towerQ O B k 0 n) N); obtain ⟨he,hp,hM⟩:= dawning K rfl H.begin hN; exact ⟨he,hp⟩
     | succ j ih=>
        obtain ⟨hv,hp,hQ,hx⟩:= H.vocals j h; obtain ⟨hr,hT⟩:= ih (by omega); exact ⟨(Rain.marching (Pike O j) _ _ T'.bind hB hr _ _ hv hx).1,sunlight (Pike O j) _ _ _ _ _ _ hv hB hr hx hT⟩ -- order
lemma voltU {j:ℕ}(hj:j< k): 0<W j ∧ Cvol (A0 j) = gain (W j)⁻¹ (towerQ O B k (j+1) n) N • Cvol (A0 (j+1)):=by
    obtain ⟨he,hv,hM,h⟩:= H.vocals j hj; exact ⟨he,(Rain.marching (Pike O j) _ _ _ hB (firms B g b A0 H hB hN j hj.le).1 _ _ he h).2⟩
end ray
variable {ℓ:Side}
open Sparks
variable {X0:Set (Grid ℓ)}{t':ℝ}
lemma trays (Y W:Pixel ℓ N)(h:Y=u • W)(he:0<u)(hz: IsOpen X0)(hV:0< (prior su ℓ).real X0)(hT:Continuous Y)(hy:realP Y)(hf:∀ V: Grid ℓ,V ∈ X0 → t'≤ (cBer W V).re)(hn:0 < t'): u*((prior su ℓ).real X0*t') ≤(Cvol Y).re:=by
   have hm:Continuous (fun i:Grid ℓ=>cBer Y i):=(peakW ℓ N).continuous.comp hT; have hI:=hm.integrable_of_hasCompactSupport (μ:=prior su _) (HasCompactSupport.of_compactSpace _); have hR:= hI.re
   have hp(i):cBer Y i=u • cBer W i:=by rw [h]; change peakW ℓ N _= _; exact map_smul ((peakW ℓ N).restrictScalars ℝ) ..
   have he':= setIntegral_mono_on (μ:=prior su ℓ) (f:=fun _=>u*t') (g:=fun i=>(cBer Y i).re) (integrable_const _) hR.integrableOn hz.measurableSet (show _ from (fun i hi=>by rw [hp]; simp only [Complex.smul_re,smul_eq_mul]; exact mul_le_mul_of_nonneg_left (hf i hi) he.le)); rw [setIntegral_const,smul_eq_mul,mul_left_comm] at he'
   exact he'.trans ((setIntegral_le_integral hR (ae_of_all _ fun i=> (hy i).2)).trans_eq (integral_re hI))
open Jets.Touch
variable {Q':ℕ→ Bed}{R':ℕ→ Towers O.L}
-- actual FINAL P donation AND positive uniform normalized denominator at x,L. instantiate in Tower
lemma shout (b:Flavor N)(Q: ConnectedActivityE6.Target su T')(h:Ω.Rates σ)(l:ℕ)(hq:0<η):∀ᶠ x:ℝ in atTop,∃ Z:ℝ,0 < Z ∧∀ k (B:SparkMesh){S':ℕ→SparkMesh} (g:PulseRide T'.bind T'.top.clip O a d S' k)(hY:Invoice g Q.table Q' R' r θ ε P Λ),B.n 0=sFirst O.L l (run O.L x) →∀ P'  (X:ℕ→SunR Ω) Y V U W A0, Stargate T' B b g P' X Y δ x η P u 0 V U W A0 → Even N → O.Branches T'.bind su →∃ (Z':ℝ)(F:Voice (towerQ O B k k 0) N),0<Z' ∧ Enn (P' k) b O.L x η (1/8) (duo F.P F.K) ∧ A0 k=Z' • songBody (T':=T') (k:=0) (i:=k) B F g (P' k) (X k) x (V k) 0 ∧Z'*Z ≤ (Cvol (A0 k)).re:=by
    filter_upwards [forecast b (passportM O.J O.order_cut) T'.top.clip O.L a d Λ σ η hq h l] with x hh
    obtain ⟨z₁,hp,he,hA,hh⟩:=hh; let t:=fiery su x O.L; let c:=sFirst O.L l (run O.L x); let Z:=(prior su c).real (stG c t)*z₁
    refine ⟨Z,mul_pos he hp,?_⟩; intro k B S' g hY hx P' X Y V U W A0 H hN hB
    let D:=towerQ O B k k 0; have hC : D=c:=by unfold D towerQ; rw [feetM]; simp [hx,c]
    obtain ⟨hF,hR⟩:=firms B g b A0 H hB hN k le_rfl; obtain ⟨h1,h2,h3,A,u',hu,hV,hx⟩:=H.costs k le_rfl; rw [H.finish.2] at hx
    have hK : delay O k k x=x:=by simp [Rails.delay,tallyK]
    rw [hK] at hV
    suffices h' :∀ (L:Side), L=c→∀ (V:Voice L N)(Z':Pixel L N),Enn (P' k) b O.L x η (1/8) (duo V.P V.K)→ Z'=u' • red V.P V.K (X k) (passportM O.J O.order_cut) (tile O k) (P' k) (g.path k) T'.top.clip (haloK O.L x) (run O.L x) 0 0 → Continuous Z' → realP Z' →u'*Z ≤ (Cvol Z').re by
       refine ⟨_,A,hu,hV,hx,h' D hC A (A0 k) hV ?_ hF hR⟩; rw [hx,H.finish.1]; unfold songBody; rw [hK]
    intro L hC V Z' hz h hZ hF; subst L; let T':= H.clock k; rw [hK] at T'; refine trays Z' _ h hu hA he hZ hF (hh _ (T'.baseG) (T'.ball) _ V (hY.he _ le_rfl).1 hz (X k) _) hp -- test syntax
end YM.QCD.Rain
