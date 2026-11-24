import YM.QCD.Stew.Rally
/-! # initial invariant projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ} {w r a u:ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset
variable {ι β:Type}(E:Gem c N ι)(b:Flavor N)
lemma lives (p q:Spike): localX o (p+q)=localX o p+localX o q:=by unfold localX; rw [ride_add]; refine congr_arg _ (funext fun i=>?_); dsimp only [Pi.add_apply]; split; exact (wave_add ..).symm; simp
noncomputable def pillar (o:Site c)(s:SampleX)(U:Grid c):Spike→L[ℂ] Sheet c:=LinearMap.toContinuousLinearMap { toFun:=fun p=> entry o p s U, map_add':=fun p q=>by rcases s with _|⟨a,_|_⟩<;> simp only [entry, Option.elim,Bool.false_eq_true, ↓reduceIte,lives, mul_add, add_mul], map_smul':=fun z p=> cores o U p s z }
noncomputable def profile (o:Site c)(s:SampleX):Sheet c→L[ℂ]Spike:=LinearMap.toContinuousLinearMap { toFun:=fun X=>shape o X s, map_add':=fun p q=>solid o p q s, map_smul':=fun t p=> metallic o p t s }
noncomputable def meter (b:Flavor N):EvenA c N→L[ℂ] Sheet c:=LinearMap.toContinuousLinearMap { toFun:=feeF b, map_add':=fun i j=>by ext x y; exact Matrix.ext_iff.mpr (grub i.val j.val) (x,b) (y,b), map_smul':=fun d i=>by ext x y; exact Matrix.ext_iff.mpr (regalia i.val d) (x,b) (y,b) }
open Port
noncomputable def nozzle (c:Side)(N:ℕ): Sheet c→L[ℂ] EvenA c N:=LinearMap.toContinuousLinearMap { toFun:=paleF N, map_add':= Port.oneC, map_smul':=fun d p=> by apply Subtype.ext; change form _ =d • form _; rw [copies_skim]; unfold form; simp only [Matrix.smul_apply, smul_eq_mul,mul_smul, Finset.smul_sum] }
lemma forceP (X:Sheet c)(b:Flavor N): feeF b (Port.paleF N X)=X:=by
   ext i j; change grasp (form (Lat.copies N X)) (i,b) (j,b)=_; exact (Matrix.ext_iff.mpr (gravid (Lat.copies N X)) (i,b) (j,b)).trans (by simp only [copies, Matrix.blockDiagonal_apply, if_true])
def bondP (i:ι)(U:Grid c):Sheet c:=∑ j: SampleX, entry (E.addr i).site (lane E b i j) j U
def backP (W:SampleX→Spike)(U:Grid c):Sheet c:=(qMass W:ℂ) • 1+(qWave W:ℂ) • freeSpin U
def mintF (V:Grid c)(i:ι): EvenA c N:=Port.paleF N (bondP E b i V)
lemma everP (he:E.Gather)(hp:Crossing E)(hv:∀ i:SampleX,Summable fun j=> ‖lane E b j i‖)(V:Grid c):HasSum (mintF E b V) (paleF N (backP (till E b 0) V)):=by
    let T:=till E b (0:Site c)
    have hh(o:Site c)(p:SampleX):HasSum (fun i=> pillar o p V (unitM E b o p i)) (entry o (T p) p V):=by
       unfold T; rw [← plums E b he hp hv o]; exact (pillar o p V).hasSum (concession E b (hv p) _).hasSum
    have h : HasSum (fun i=>bondP E b i V) (backP T V):=by
       unfold backP; unfold T; rw [← Stew.total (portraits E b he hp hv)]
       apply (hasSum_sum (s:=univ) fun o _=> hasSum_sum (s:=univ) fun p _=> hh o p).congr_fun; intro i; unfold bondP; symm; rw [sum_comm]; apply sum_congr rfl; intro j _; rw [sum_eq_single (E.addr i).site]; · rw [show unitM E b (E.addr i).site j i=lane E b i j from if_pos rfl]; rfl
       · intro a _ ha; rw [unitM,if_neg ha,map_zero]
       simp
    exact (nozzle c N).hasSum h
lemma rotUp (x y:Spike)(t:SampleX)(o:Site c)(hp:Warrant v g k)(U:Grid c)(ht:y=skySig v.1 t • (k*x*star k)): entry o x t (sky v U)= haze v k g*entry (act v o) y (Stew.tide v.1 t) U *star (haze v k g):=by
    rw [ht,← freshE o x t U hp, Matrix.mul_assoc, (trail hp).2,mul_one] -- .2 correct
lemma turnC (v: Strut c)(k:Spike)(g: Site c→ℂ)(hp:Warrant v g k)(i j:ι)(h:E.addr j=rotateL (E.addr i) v)(hr:∀ U, Diode N v k g (E.view i (sky v U))= E.view j U)(he:Gated (E.addr i).support (E.view i 1))(hx: Fit (E.view i 1))(hv: shadeG (E.view i))(V:Grid c): Diode N v k g (mintF E b (sky v V) i)= mintF E b V j:=by
    apply Port.rayTrade (copies N (haze v k g)) (copies_unitary _ _ (trail hp)) _ _
    have hz(a): lane E b j (tide v.1 a)=skySig v.1 a •(k*lane E b i a*star k):=by unfold lane; rw [h]; exact Stew.whirl b (E.addr i) (E.view i) _ a hp hx hr hv he -- syntax
    rw [←copies_star,← Lat.copies_mul,← Lat.copies_mul]; apply congr_arg
    unfold bondP; nth_rw 2 [← Equiv.sum_comp (tide v.1)]; rw [Matrix.mul_sum,Matrix.sum_mul,h]; refine sum_congr rfl fun i hi => rotUp _ _ i _ hp V (hz i)
lemma warpR (h: Dyed E)(i U): Regal c N (mintF E b U i)=mintF E b U i:=by
    let X:= bondP E b i U
    have hv:X=chirality c*star X*chirality c:=by
       let v: Equiv.Perm SampleX:=⟨Stew.invert,Stew.invert,Stew.inv_inv,Stew.inv_inv⟩
       have hh s:lane E b i (v s)=g5*star (lane E b i s)*g5:=headQ b _ _ _ (h.num i _) (h.gauge i) (h.real i _)
       unfold X bondP; nth_rw 1 [← Equiv.sum_comp v]; simp only [star_sum, Matrix.mul_sum, Matrix.sum_mul] -- edit
       exact sum_congr rfl fun j _=>by rw [hh]; exact tiltE ..
    apply Subtype.ext; change disguise _ (surf _ (form (Lat.copies N X)))=form _; rw [Port.surf_form,disguise,form_map, Matrix.transpose_transpose]; apply congr_arg
    change star (Lat.copies N _) * (_ * Lat.copies N _)=_; rw [← copies_star,← copies_star,← copies_mul,← copies_mul]; simp only [Lat.chi_star]; exact congr_arg _ ((Eq.trans (Matrix.mul_assoc ..).symm hv.symm))
lemma gainR (i): shadeG (fun V=>mintF E b V i):=by
    intro U k; let q:=siteRot k; let X:=bondP E b i U; let y:=bondP E b i (gauge k U); have he:y*q=q*X:=by unfold y X bondP; rw [Matrix.mul_sum, Matrix.sum_mul]; exact sum_congr rfl fun j _=> gateE ..
    have hh : y=q * X*star q:=by rw [← he,Matrix.mul_assoc, (siteRot_u k).2,mul_one]
    apply congr_arg Subtype.val (Port.rayTrade (Lat.copies N q) (copies_unitary _ _ (siteRot_u k)) y X ?_); rw [hh]; rw [copies_mul,copies_mul,copies_star]
lemma form_fit (X:Sheet c)(F:ℕ):Fit (Port.paleF F X):=by
    intro W h; apply Port.rayTrade _ (unit_f h) X X; rw [show (_ * Lat.copies F X)=_ from Sway.column X W, Matrix.mul_assoc,(unit_f h).2,mul_one]; rfl
lemma form_card (X:Sheet c)(F :ℕ):coef ∅ (light _ (Port.paleF F X))=0:=spectrum (form_two _) _ (by simp)
lemma addressT (hn:4 ≤ c.val) (i:ι)(k:SampleX):shape (E.addr i).site (feeF b (mintF E b 1 i)) k=lane E b i k:=by
    rw [mintF,forceP]; unfold bondP; change profile _ k _=_; rw [map_sum,sum_eq_single k]
    · rw [show profile _ k _=_ from Stew.both (E.addr i).site hn (lane E b i k) k k, if_pos rfl]
    · intro j _ hj; exact (Stew.both _ hn _ _ _).trans (if_neg hj.symm)
    simp
end YM.QCD.Stew
