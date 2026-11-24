import YM.Cardinal.Doss
/-! # Singleton report tape, parity generalized. With mask bill requiring on-mask sizes only. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t t₁ t₂:ℝ}{O: BudgetPoint}
namespace Card
namespace Iris
variable {q:Bool} (N)(o:Site c)
local notation "M"=> Ribbon.ample N Unit
local notation "T"=> topM
local notation "Vk"=> goldM q
local notation "K"=> Keys c N
local notation "R"=> Spine Iris.alpha
local notation "B!"=>Patio (Keys c N ⊕ Spine Unit)
local notation "p!"=>pluck K (goldM q)
set_option quotPrecheck false
open QCD.Stew
-- Singleton Report coefficients. products of markers vanish. Film.Linearity pack free.C
open NormedSpace
variable (F: Patron.Rail c N E)(Y:Film c N Unit J)(S:Support c)
variable (V:Grid c)
noncomputable local instance : Fintype (Cove.Hat c):=Fintype.ofFinite _
local notation "N'"=> banknote N (fun _:Unit=>o) v
local notation "E⁺"=>rootR R K
local notation "e₀"=> E⁺ (Kites.heartK F t V)
local notation "W₀"=> Wcall N F Y V (t:=t)
variable (D:Grid c→ EvenA c N)
lemma energy (X:Reel c N Unit U)(hp:X.Book (fun _=>o) (fun _=>q)) (hz:Y.Beat N (fun _=>o) (fun _=>q) t) (hv:Summable fun i=>‖Y.mark i V‖)(he:Summable fun i=> ‖F.warp i V‖) :
    let Ψ:= Wcall N F Y V (t:=t) + (Reel.rope X t V)*E⁺ (heartK F t V)
    relativeE N X Y F D t V= E⁺ (NormedSpace.exp (D V)*heartK F t V)+ E⁺ (NormedSpace.exp (D V)) * Ψ ∧ Polite (fun _:alpha=>q) T Ψ :=by
    intro Ψ; obtain ⟨hG,hT⟩:= scores N o F Y V hz hv he; let G:= Reel.rope X t V
    have heer (i:U):Polite (fun _:Unit=>q) T (Reel.mist X t i V):=by
         unfold Reel.mist; by_cases h: Healthy t (X.addr i).support V; · rw [masked_eq _ _ _ _ h]; exact (itt _ (hp.stays i)) ▸ (hp.stage ..).1
         rw [masked_ne _ _ _ _ h]; exact polite_nil ..
    have hf: Polite (fun _:alpha=>q) T G:=polite_tsum heer
    constructor
    · unfold relativeE Ψ; rw [exp_add,← map_exp (E⁺) (E⁺).toLinearMap.toContinuousLinearMap.continuous,honor_exp N q (Reel.rope X t V) hf,hG,map_mul]; let Zp:=E⁺ (NormedSpace.exp (D V)); -- let V shorthand
      change Zp*(1+ G)*(e₀+ W₀)= Zp* (e₀)+Zp*( W₀+G* (e₀)); rw [mul_assoc]; rw [add_mul,one_mul,mul_add G, hf.nilpotent hT (by simp [topM]),add_zero,add_assoc,mul_add]
    apply hT.lays; -- cast using eq_mp
    have ht:=hf.attached (rootE N q (heartK F t V)); exact (Finset.union_empty T) ▸ ht
variable {U₁ Bp:Type}
local notation "r'"=> (fun _:alpha=>q)
local notation "p'"=> (fun _:alpha=>o)
lemma markedMatter (X:Reel c N Unit U)(hp:X.Book (fun _=>o) (fun _=>q))(hz:Y.Beat N (fun _=>o) (fun _=>q) t)(hv:Summable fun i=>‖Y.mark i V‖)(he:Summable fun i=> ‖F.warp i V‖) :
    let Ψ:= Wcall N F Y V (t:=t) + (Reel.rope X t V)*E⁺ (heartK F t V)
    pluck K (goldM q) (relativeE N X Y F D t V)= pluck K (goldM q) (E⁺ (NormedSpace.exp (D V))*Ψ) ∧ pluck K (∅:Finset (Spine alpha)) (relativeE N X Y F D t V)=light K (NormedSpace.exp (D V) * heartK F t V):=by
    intro Ψ; obtain ⟨hP,hX⟩:=energy N o F Y V D X hp hz hv he; rw [hP,map_add,map_add]; let QG:= E⁺ (NormedSpace.exp (D V)* heartK F t V); let Z:= E⁺ (NormedSpace.exp (D V)); have hz:Polite r' T (Z*Ψ):= (empty_union T) ▸ ((rootE N q _).attached hX) -- diag complex.It only parity sign hF
    refine ⟨?_,?_⟩
    · rw [show pluck K (goldM q) QG=0 from (rootE N q _).spectral _ ((burst_absent r').symm ▸ (engaged q).ne_empty)] -- rw pattern macro QG local failed
      rw [zero_add]
    rw [show pluck K (∅:Finset R) (Z*Ψ)=0 from hz.spectral _ (engaged q).ne_empty.symm,add_zero]; exact (revive ..).symm.trans (frozen ..)
-- Combine stamps under same parity, position (lift sign already in s), use one after with Pad.Order. Inclusion in Seat expansions for general n-arm may require separate book.
noncomputable def addReel (X:Reel c N I J)(Y: Reel c N I U): Reel c N I (J⊕U):=⟨Sum.elim X.addr Y.addr,Sum.elim X.z Y.z,Sum.elim X.mark Y.mark⟩
noncomputable def addFilm (X:Film c N I J)(Y: Film c N I U): Film c N I (J⊕U):=⟨Sum.elim X.addr Y.addr,Sum.elim X.z Y.z,Sum.elim X.mark Y.mark⟩
noncomputable def feeR (X: Reel c N Unit J)(u:ℂ): Reel c N Unit J:=⟨X.addr,X.z,fun i=>u • X.mark i⟩
noncomputable def feeK (X: Film c N Unit J)(u:ℂ): Film c N Unit J:=⟨X.addr,X.z,fun i=>u • X.mark i⟩
set_option maxRecDepth 6000 in
lemma ready_plus (p:I→Site c)(qP:I→Bool) (X:Reel c N I J)(Y:Reel c N I U)(hp:X.Book p qP)(hz:Y.Book p qP) : (addReel N X Y).Book p qP :=by
    constructor
    · rintro (i|i); exact hp.stays i; exact hz.stays i
    · rintro (i|i); exact hp.stamp i; exact hz.stamp i
    · rintro (i|i); exact hp.permit i; exact hz.permit i
    · rintro (i|i); exact hp.room i; exact hz.room i
    · rintro (i|i); exact hp.stage i; exact hz.stage i
    · rintro (i|i) <;> simp only [addReel, Sum.elim_inl, Sum.elim_inr]; exact hp.tint i; exact hz.tint i
set_option maxRecDepth 6000 in
lemma beat_plus (p:I→Site c)(qP:I→Bool)(Y:Film c N I J) (X:Film c N I U)(hP:X.Beat N p qP t)(hY:Y.Beat N p qP t): Film.Beat N p qP (addFilm N Y X) t :=by
    constructor
    · rintro (i|i); exact hY.commits i; exact hP.commits i
    · rintro (i|i); exact hY.spark i; exact hP.spark i
    · rintro (i|i); exact hY.matters i; exact hP.matters i
    · rintro (i|i); exact hY.reads i; exact hP.reads i
    · rintro (i|i) <;> simp only [addFilm, Sum.elim_inl, Sum.elim_inr]; exact hY.color i; exact hP.color i
    · rintro (i|i); exact hY.mask i; exact hP.mask i
    · rintro (i|i); exact hY.budget i; exact hP.budget i
lemma may (x:Patio (Keys c N⊕Spine Unit))(W:Support c)(S:Finset Unit)(s:ℂ)(h: Stitch.lights S W (fun _=>o) (fun _=>q) x) : Stitch.lights S W p' r' (s • x):=by
    refine ⟨h.1.smooch _,fun i=> ?_⟩; change pluck K i (s • x)∈_; rw [map_smul]; exact Subalgebra.smul_mem _ (h.2 i) _
set_option maxRecDepth 6000 in
lemma ready_by (X:Reel c N Unit J)(hp:X.Book (fun _=>o) (fun _=>q))(u:ℂ): (feeR N X u).Book p' r':= ⟨hp.stays,hp.stamp,fun i=> measurable_const.smul (hp.permit i),fun i p q he=> congr_arg (u • ·) (hp.room i _ _ he),fun i V=> may N o _ _ _ u (hp.stage i V),fun i V k=> (map_smul (parcelColor N k Unit) _ _).trans (congr_arg (u •·) (hp.tint ..))⟩
set_option maxRecDepth 6000 in
lemma beat_by (hp:Y.Beat N (fun _=>o) (fun _=>q) t)(u:ℂ): (feeK N Y u).Beat N p' r' t:= ⟨hp.commits,hp.spark,fun i=> measurable_const.smul (hp.matters i),fun i p q hv he=> congr_arg (u • ·) (hp.reads i _ _ hv he), fun i U k=> (map_smul (parcelColor N k Unit) _ _).trans (congr_arg (u •·) (hp.color ..)), fun i V hn=>hp.mask i V (fun h=>hn (show u • Y.mark i V=0 by rw [h,smul_zero])),fun i V=> may N o _ _ _ u (hp.budget i V)⟩
lemma addK_rit (X:Film c N Unit U)(hX:Summable fun i=>‖X.mark i V‖)(hP:Summable fun i=>‖Y.mark i V‖) : Wcall N F (addFilm N Y X) V (t:=t)=W₀+ Wcall N F X V (t:=t):=by
   unfold Wcall; rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; have h(x :Hat c): coin (addFilm N Y X).addr (fun i=> (addFilm N Y X).mark i V) x=coin Y.addr (fun i=>Y.mark i V) x+coin X.addr (fun i=>X.mark i V) x :=by apply Eq.trans ?_ (Film.coin_merge Y.addr X.addr (fun i=>Y.mark i V) (fun i=> X.mark i V) hP hX x); apply congr_arg (fun f: J⊕U → Patio (Keys c N⊕Spine Unit) =>coin _ f _); funext a; rcases a with a|a <;> rfl
   unfold billK; split; simp_rw [h,add_mul,sum_add_distrib]; rw [add_zero]
lemma feeK_rit (u:ℂ)(hp:Summable fun i=>‖Y.mark i V‖): Wcall N F (feeK N Y u) V (t:=t)=u • W₀:=by
    unfold Wcall; rw [Finset.smul_sum]; apply sum_congr rfl; intro i _; unfold billK; split; rw [Finset.smul_sum]; refine sum_congr rfl fun j _=>?_; rotate_left
    · rw [smul_zero]
    have he: coin (feeK N Y u).addr (fun i=> (feeK N Y u).mark i V) j= u • coin Y.addr (fun i=> Y.mark i V) j:= ((show Summable (fun i:↥(ray Y.addr j)=> Y.mark i.val V) from hp.of_norm.comp_injective Subtype.val_injective).hasSum.const_smul u).tsum_eq -- specify via `g:` param
    rw [he,smul_mul_assoc]
lemma rope_plus (X:Reel c N Unit U)(Y:Reel c N Unit J)(hp:Summable (fun i=> Reel.mist X t i V))(hz:Summable fun i=>Reel.mist Y t i V): Reel.rope (addReel N Y X) t V=Reel.rope Y t V+Reel.rope X t V:=(hz.hasSum.sum (f:=fun i=>Reel.mist (addReel N Y X) t i V) hp.hasSum).tsum_eq
lemma rope_by (X:Reel c N Unit U)(u:ℂ)(hp:Summable (fun i=> Reel.mist X t i V)): Reel.rope (feeR N X u) t V = u • Reel.rope X t V:=by
    apply HasSum.tsum_eq; refine HasSum.congr_fun (hp.hasSum.const_smul u) ?_; intro i; by_cases he: Healthy t (X.addr i).support V; · rw [Reel.mist,masked_eq _ _ _ _ (show Healthy t ((feeR N X u).addr i).support V from he)]; change u • (X.mark i V) = _; rw [Reel.mist,masked_eq _ _ _ _ he]
    rw [Reel.mist,masked_ne _ _ _ _ (show ¬ Healthy t ((feeR N X u).addr i).support V from he)]; rw [Reel.mist,masked_ne _ _ _ _ he,smul_zero]
end Iris
end Card
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Card.Iris.markedMatter
