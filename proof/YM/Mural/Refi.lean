import YM.Mural.Bison
/-!
# Spectral mixing from the turns
 Computation in column space at a fixed grid; row sums one keeps neutral. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat
open PaletteT Ribbon
variable {c f:Side}{j k m:ℕ} {V:Type*} [NormedCommRing V] [NormedAlgebra ℂ V]
noncomputable def zoneD (A B:Mat)(z:ℂ) : Delta Rank:= fun i j=> match i with
  | none=> if j=none then 1 else 0
  | some i=> match j with | none=> 1- ∑ k:Rank,z*doll A B i k | some k=> z*doll A B i k
variable (A B:Mat)(z:ℂ)
lemma loans : PaletteT.straight (zoneD A B z):=by
   intro i; cases i with| none=> simp [zoneD] | some i => rw [Fintype.sum_option]; simp [zoneD]
lemma trust (x:Option Rank→ V)(hx:x none=0) (i:Option Rank): aggregate (fun j=>zoneD A B z i j) x= muster A B z x i:=by
   unfold aggregate; cases i with| none=> simp [hx,zoneD,muster]|some i=> rw [Fintype.sum_option,hx,smul_zero,zero_add]; unfold muster tot zoneD; dsimp only; simp_rw [mul_smul]; rw [Finset.smul_sum]
lemma tis (x:Option Rank→V)(hx:x none=0):Binds (zoneD A B z) (AlgHom.id ℂ V) (muster A B z x) x:=fun i=> (trust A B z x hx i).symm
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist Kites Creek Cove
variable {f:Side}{I E:Type}{N:ℕ} (Z:PrintR f N Rank I E) (D₁ D₂: Grid f→ Mat)
local notation "Ψ"=> Tine f N Unit
local notation "Tz"=> trestle Z D₁ D₂ z
local notation "Z★" i=>PrintR.regE Tz i
local notation "Y★" i=> PrintR.regK Tz i
open Push.AbsoluteSums
variable (U:Grid f)(O:BudgetPoint){η:ℝ}
local notation "Zt"=>zoneD (D₁ U) (D₂ U) z
local notation "κ"=>Cove.Keys f N
local notation "R"=> Ribbon.Spine Unit
variable (V:Unit→Site f)(S:Support f) (Gg:Lat.Frame f→ PaletteT.Delta Rank)(H:Z.Fides V S O Gg)
local notation "Uκ"=> rootR (Spine Unit) (Cove.Keys f N)
include H
lemma sp_E (i:I):
    Binds Zt (AlgHom.id ℂ (Tine f N Unit)) (fun j=> Reel.mist (PrintR.regE (trestle Z D₁ D₂ z) j) O.threshold i U) (fun j=> Reel.mist (Z.regE j) O.threshold i U) ∧ Loose qT (fun j=> Reel.mist (Z.regE j) O.threshold i U):=by
       let h:= H.tinted (fun _=>1)
       let xj(j):= Reel.mist (Z.regE j) O.threshold i U; have hp:xj none=0:= h.neutral i U; simp_rw [vellum]; refine ⟨tis (D₁ U) _ _ xj hp,tur (fun _=>0) xj (T:=Z.srcE.z i) (Or.inl hp) (fun j=>?_) ?_⟩
       · let G:= (Z.regE j); change Polite qT (G.z i) (G.mist O.threshold i U); unfold Reel.mist; by_cases hh:Healthy O.threshold (G.addr i).support U; rw [masked_eq _ _ _ _ hh]; exact ((h.blocking j).stage i U).1; rw [masked_ne _ _ _ _ hh]; exact polite_nil ..
       intro he; exact False.elim ((h.blocking (none:Option Rank)|>.stays i).ne_empty he)
lemma sp_K (i:E): Binds Zt (AlgHom.id ℂ (Tine f N Unit)) (fun j=> (Y★ j).mark i U) (fun j=> (Z.regK j).mark i U) ∧ Loose qT (fun j=> (Z.regK j).mark i U):=by
       let h:= H.rise (fun _=>1); let p j:=(Z.regK j).mark i U; have hp : p none=0:= h.unit i U; have hj j: (Y★ j).mark i U=muster (D₁ U) (D₂ U) z p j:=rfl
       simp_rw [hj]; exact ⟨tis _ _ _ p hp,tur (fun _=>0) p (T:=Z.srcK.z i) (Or.inl hp) (fun j=> ((h.blocking j).budget i U).1) (fun he=>False.elim ((h.blocking (none:Option Rank)|>.commits i).ne_empty he))⟩
omit H
lemma billP (t θ b d p v h:ℝ) (hp:Z.Levy O θ t b d p v h)(ht:1 ≤ t)(hv:1 ≤v)(he:1 ≤θ)(hb:0 ≤ b)(hd:0≤d):∀ i:Option Rank,Summable (fun j:I=> ‖(Z.regE i).mist O.threshold j U‖)∧ Summable (fun j=> ‖Z.etaK i j U‖):=by
    have hs(y:Ψ): ‖y‖ ≤ Tablet.credits t y:= Tablet.minimal _ _ (by rintro (j|j); exact ht; exact le_rfl) _
    intro i; obtain ⟨f,hf,hX⟩:=hp.budget i; obtain ⟨g,h₁,hS⟩:= (hp.fare i).price
    let E0:= Z.regE i; let G:= Z.regK i; have hh:0 ≤ g:= fun i=> (Creek.load_nn ..).trans (h₁ i U); have h0:Summable f := Loom.fishes _ _ hX (fun i=>(repay_pos ..).trans (hf i U)) hb (fun i _=>⟨_,(E0.addr i).anchor⟩)
    let h' : G.Stock N O.B v d t h (fun _=>1):=hp.fare i; let w:= Film.fares N G g (fun _=>1) v; have hV(j):g j ≤ w j:= by unfold w Film.fares GasP.taxed; simp only [prod_const_one,abs_one,one_mul]; exact le_mul_of_one_le_left (hh j) (one_le_pow₀ hv)
    have hj:Summable w:= Loom.fishes _ _ hS (fun i=> (hh i).trans (hV i)) hd fun i _=>(G.addr i).alive.mono (G.addr i).part
    constructor; · refine Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun j=> (hs _).trans ((minor _ _ _ _ he ?_ _).trans (hf j U))) h0; rintro (j|j); exact zero_lt_one.trans_le ht; exact one_pos
    exact Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun j=> (hs (Z.etaK i j U)).trans ((h₁ j U).trans (hV j))) hj
variable {J:Type}(P: Patron.Rail f N J)(W:Grid f→ EvenA f N) (hp:∀ i:Option Rank,Summable fun j=> ‖(Z.regE i).mist O.threshold j U‖)(hQ:∀ i:Option Rank,Summable fun j=> ‖Z.etaK i j U‖) (hz:∀ i:Option Rank,Summable fun j=> ‖Reel.mist (PrintR.regE (trestle Z D₁ D₂ z) i) O.threshold j U‖)(hV:∀ i:Option Rank,Summable fun j=> ‖(trestle Z D₁ D₂ z).etaK i j U‖)(hK:Summable fun i=> ‖P.warp i U‖)
open NormedSpace
lemma stocked (x:Patio κ): Loose qT (fun _:Option Rank=>Uκ x):=by
   have h:Polite qT ∅ (Uκ x):=by unfold Polite; rw [burst_absent]; exact ⟨_,quiet ..⟩
   exact ⟨h,fun _=>ValidPieces.role _ h (subset_univ _),fun _=>rfl⟩
lemma hoardR (G:PrintR f N Rank I E)(i:Option Rank)(hp: Summable (fun j=> ‖G.etaK i j U‖))(he:Summable (fun j=>‖P.warp j U‖)) : Summable (roof (Film.addressSets N (G.regK i) P) (fun j=>Film.spruced N (G.regK i) P j U) (RG.flags O.threshold U)):=by
    apply Plate.rum
    let p j:=Uκ (P.warp j U); have hp':Summable (fun j=> ‖p j‖):= ((Uκ).toLinearMap.toContinuousLinearMap.hasSum (he.of_norm.hasSum)).summable.norm
    exact Summable.sum _ hp' hp
include H hp hQ hz hV hK
set_option maxHeartbeats 560000 in
lemma silhouettes : Binds Zt (AlgHom.id ℂ (Tine f N Unit)) (fun i=> relativeE N (PrintR.regE (trestle Z D₁ D₂ z) i) (PrintR.regK (trestle Z D₁ D₂ z) i) P W O.threshold U) (fun i=> relativeE N (Z.regE i) (Z.regK i) P W O.threshold U)∧ Loose qT (fun i=> relativeE N (Z.regE i) (Z.regK i) P W O.threshold U) :=by
    let H' := graph (P:=Rank) qT (Cove.Keys f N); let A i j:=Reel.mist (Z.regE i) O.threshold j U; let B i j:=Reel.mist (Z★ i) O.threshold j U; let x : Ψ:= Uκ (W U); let u i:= x+ ∑' j,A i j; let y i:=x+∑' j,B i j; let q:= Zt
    have ht: PaletteT.straight q:=loans (D₁ U) (D₂ U) z; let Id:= AlgHom.id ℂ Ψ
    have hb j:= sp_E z Z D₁ D₂ U O V S Gg H j
    have hx : Loose qT u:= Loose.crest (stocked _ ) (show Loose _ (fun i=>∑' j,A i j) from entrance H' (fun j i=>A i j) (fun i=>(hb i).2) fun i=> (hp i).of_norm)
    have hg:Binds q Id y u:= binds_up q _ (unity q Id ht x x rfl) (binds_tsum q Id (fun j i=> B i j) (fun j i=>A i j) (fun i=>(hb i).1) (fun i=>(hz i).of_norm) fun i=> (hp i).of_norm)
    have hO:(fun _:Option Rank=>(1:Ψ))∈ H':= Loose.oneV ..; have hT(m)(h:m∈ H')(n)(g:n∈H') : m*n∈ H':= Loose.light (show Loose _ _ from h) g; have hE(m)(h:m∈H')(n)(g:n∈H')(i j): (m i-m none)*(n j-n none)=0:=fare (show Loose _ _ from h) g i j
    let fv i:=exp (y i); let g i:=exp (u i)
    have he:Binds q Id fv g := binds_exp q Id H' hO hT hE hg ht hx
    let v i (j:J⊕ E):Ψ:= Film.spruced N (Z.regK i) P j U; let p i j:= Film.spruced N (Y★ i) P j U; let X:J⊕E→ Cove.Hat f:= Film.addressSets N (Z.regK (none:Option Rank)) P
    let m i k:= Plate.roof X (v i) (RG.flags O.threshold U) k; let m' i k:= Plate.roof X (p i) (RG.flags O.threshold U) k; let g' i:=∑' j,m i j; let f' i:= ∑' j,m' i j
    have hl j:Binds q Id (fun i=> p i j) (fun i=> v i j)∧ Loose qT (fun i=> v i j):=by
          rcases j with j|j; exact ⟨unity _ _ ht _ _ rfl,stocked _⟩; exact sp_K z Z D₁ D₂ U O V S Gg H j
    have hs(j):Binds q Id (fun i=>m' i j) (fun i=>m i j)∧ Loose qT (fun i=>m i j):=by
          unfold m m' Plate.roof; split; swap; · exact ⟨unity _ _ ht _ _ rfl,H'.zero_mem⟩
          exact ⟨binds_prod q Id H' hO hT hE _ _ _ (fun i _=>(hl i).2) (fun i _=>(hl i).1) ht, gatheredX H' _ _ (fun i _=>(hl i).2) hO hT⟩
    have hm i:Summable (m i):= hoardR U O P Z i (hQ _) hK; have hm' i: Summable (m' i):=hoardR U O P Tz i (hV _) hK
    have hu: Loose qT g:= live_pow qT u hx; have hh: g'∈ H':= entrance H' (fun j i=>m i j) (fun i=>(hs i).2) hm
    exact ⟨binds_mul q Id ht he (show Binds q Id f' g' from binds_tsum q Id (fun j i=>m' i j) _ (fun j=>(hs j).1) hm' hm) (hE _ hu _ hh), Loose.light hu (show Loose _ _ from hh)⟩
end YM.QCD.Comet
#print axioms YM.QCD.Comet.silhouettes
