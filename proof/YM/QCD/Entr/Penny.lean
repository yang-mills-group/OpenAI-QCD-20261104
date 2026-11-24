import YM.QCD.Entr.Stage
/-! # position price & wave earnings at finite c. Uniformity of all purchased components. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Eyrie Rudder Sparks Pearl YM.Next.Free Bloch Laurent
variable {Γ:Silo c}{A: BankP c}{U:St c}
structure AnchorT {ι:Type}(G: Gem c N ι)(p:BudgetPoint)(a σ C:ℝ) : Prop where
    peg : ∃ f:ι→ℝ,Anchored (fun i=>(G.addr i).site) f (fun i=>coverNumber p.B (G.addr i).support) σ C ∧∀ i,Woven (G.addr i).site (G.addr i).support p a (G.view i) (f i) ∧∀ U, Sen (G.addr i).site a (G.view i U)≤ f i
lemma AnchorT.law {ι:Type}{G: Gem c N ι} (h:AnchorT G p a u r): Licence p u r a G :=by obtain ⟨f,hf,h⟩:= h.peg; exact ⟨f,hf,fun i=>(h i).1⟩
lemma Licence_g {ι:Type}{G: Gem c N ι}(h: Licence p u r a G): G.Gather:=by obtain ⟨f,hf,h⟩:=h.zone; exact ⟨fun i=> (h i).room,fun i=> (h i).Borel, fun i=>(h i).gated⟩
lemma floating (B R n N:ℕ):∃ C:ℝ, 1 ≤ C ∧∀ (c:Side)(A:BankP c)(Γ:Silo c)(δ η a q:ℝ)(U:St c), Run.Pack id id η δ B U q Γ A →∀ p:BudgetPoint,p.order≤n→p.power≤R→p.threshold ≤ η→ B≤p.B→0<a→∀ σ:ℝ, 0 ≤ σ → σ+1≤δ → AnchorT (sealG Γ N) p a σ (C*a^2*q) :=by
    obtain ⟨C,hc,H⟩:= forged B R n N; obtain ⟨K,hK,h⟩:=applause B R n
    refine ⟨max 1 (2*C*K),le_max_left ..,fun c A Γ δ η a q U hP p hn hr hv hB ht σ hσ hδ=>?_⟩
    let Y:=faceQ A C a B R n; have hh(q:Tick c):0≤ silos A q:=need hP q; have hy:0≤q:= (Finset.sum_nonneg (s:=univ) (f:=fun j=>duel A 0 j δ B) (fun i _=>Finset.sum_nonneg fun X _=>mul_nonneg (fair ..).le (hh (0,i,X)))).trans (hP.spends _)
    refine ⟨Y,fun i=> Extra.Iteration.Cost.enlarge (auctions hP (p.threshold_pos.trans_le hv) hc (h c) hσ hδ hB (zero_le_one.trans hK) (t:=a) i) ?_,fun i=> H _ _ _ _ _ _ _ _ hP p hn hr hv ht i⟩
    have hM : C*a^2*K*(q+q)=(2*C*K)*a^2*q:=by ring
    rw [hM]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (sq_nonneg _)) hy
noncomputable def sparkR (P: Spike):ℝ:= ((Lat.gamma 0 * P) (0,0) (0,0)).re
lemma wake (x:SampleX→Spike): qWave x=sparkR (Jot x):=by unfold qWave sparkR Jot; rw [mul_sub]; rfl
noncomputable def sparkL : Spike →L[ℝ] ℝ:= LinearMap.toContinuousLinearMap { toFun:=sparkR,map_add':=fun P Q=>by unfold sparkR; rw [mul_add]; rfl,map_smul':=fun z P=>by unfold sparkR; rw [Matrix.mul_smul]; simp }
lemma spot : sparkL (Lat.gamma 0)=1:=by change sparkR _=_; unfold sparkR; rw [Lat.gamma_sq]; simp
lemma spars (T:Plan j):∃ C:ℝ,0<C∧∀ (c:Side) (v:Train j), c.val* ‖torque c (Pine.wood T 0 v 1)-Fintype.card (Site c) • Lat.gamma 0‖ ≤ Fintype.card (Site c)*C:=by
    obtain ⟨δ,W,hd,hW,H⟩:= pays_all T; let η:=δ/4; let C:= 1+4*Reserves.polyPrice (4*η) 2 * W; have he:0<η:=by unfold η; positivity
    refine ⟨C,by unfold C Reserves.polyPrice; positivity,fun n v=> ?_⟩
    obtain ⟨I,G,hp,H⟩:= H v; have he':4*η=δ:=by unfold η; ring
    apply (wagesV he (show Rudder.Wages (4*η) W G from he'.symm ▸ hp) H n).trans; unfold C; nlinarith [show (0:ℝ) ≤ Fintype.card (Site n) from Nat.cast_nonneg _]
-- works any N positive
lemma wager (T:Plan j)(B:ℕ)(X:ℝ):∃ M:ℕ,∀ F: Train j,∀ c:Side,M≤ c.val→∀ (A:BankP c)(Γ:Silo c)(η e:ℝ)(N:ℕ),0<η→1≤e→ Run.Pack id id η e B (Pine.wood T 0 F) X Γ A→Torch Γ→(sealG Γ N).Gather→∀ (b: Flavor N)(p:BudgetPoint), B≤ p.B→ let Y:=till (sealG Γ N) b 0
    |qWave Y-1| ≤ (1/4:ℝ):=by
    obtain ⟨W,hW,H⟩:= spars T
    obtain ⟨K,hK,h⟩:= applause B 0 0
    let d:= 10*‖goldL‖*K*(X+X); obtain ⟨M,hM⟩:= exists_nat_gt (4*(‖sparkL‖*(W+d)))
    refine ⟨M,fun F c hP A Γ η e N he hq ht hT hG b p hX=>?_⟩; intro Y
    let U:= torque c (Pine.wood T 0 F 1); let k:ℕ:=Fintype.card (Site c); have hp:=H c F; have hx : c.val*‖U-k • Jot Y‖ ≤ k*d:=priceζ ht hT he K hq hK (h c) b p hX hG
    let f:=k • (Jot Y-Lat.gamma 0); have hz:f=(U-k • Lat.gamma 0)-(U-k • Jot Y):=by unfold f; rw [nsmul_sub]; abel
    have hv : c.val * ‖f‖≤ k*(W+d):=by rw [hz]; apply (mul_le_mul_of_nonneg_left (norm_sub_le ..) (Nat.cast_nonneg _)).trans; rw [mul_add]; exact (add_le_add hp hx).trans_eq (mul_add ..).symm
    let A:ℝ:=c.val; let B:ℝ:= k; have ha:0<A:= by unfold A; positivity
    have hb:0<B:=by unfold B k; positivity
    have he: ‖sparkL f‖= (k:ℝ)*|qWave Y-1|:=by unfold f; rw [map_nsmul,map_sub,wake,spot]; change ‖k • (_:ℝ)‖=_; rw [nsmul_eq_mul,norm_mul]; rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]; rfl
    have hV : (4:ℝ)*‖sparkL‖*(W+d) ≤A:=by unfold A; apply le_trans _ (Nat.cast_le.mpr hP); linarith only [hM]
    refine le_of_mul_le_mul_left ?_ (show 0<A*B from mul_pos ha hb); rw [mul_assoc A B,show (B*|qWave Y-1|)= ‖sparkL f‖ from he.symm]; apply (mul_le_mul_of_nonneg_left (sparkL.le_opNorm f) ha.le).trans; change A*‖f‖≤ B*(W+d) at hv; linarith only [mul_le_mul_of_nonneg_left hv (norm_nonneg sparkL),mul_le_mul_of_nonneg_right hV hb.le] -- unfold A
end YM.QCD.Entr
