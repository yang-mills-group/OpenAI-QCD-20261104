import YM.QCD.Entr.Que
/-! # amplitude directions fixed. E pressure & mask subtraction all U. Costs scaled pre. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z:ℝ}{i j o:Site c}{X:Support c}
open Revolve Villa Port Reserves Footprint
variable {Γ:Silo c}{A: BankP c}{U:St c}
lemma applause (B R n:ℕ): ∃ K:ℝ,1≤K∧∀ (c:Side) (X:Support c), tribute B R n X ≤ K*rent 1 B X:=by
   let k:=2+R*n; let a:ℕ:=1+6*B+2; let K:= (a:ℝ)^k*polyPrice 1 k; refine ⟨max 1 K,le_max_left ..,fun c X=> ?_⟩
   let b:= coverNumber B X; have h : 1 + diameterQ B X ≤ a*(1+b):=by unfold diameterQ; change 1+(b*_+_) ≤ _; unfold a; nlinarith
   unfold tribute; apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right 1 K) (fair ..).le); unfold K rent; have he : (1+ (b:ℝ))^k ≤ polyPrice 1 k * Real.exp (1*b):= polynomial_cost zero_lt_one (by positivity) k
   apply (pow_le_pow_left₀ (by positivity) (by exact_mod_cast h : (1:ℝ)+(diameterQ B X:ℝ) ≤ (a:ℝ)*(1+b:ℝ)) k).trans; rw [mul_pow, mul_assoc]; exact mul_le_mul_of_nonneg_left he (by positivity)
lemma entriesU (h:Run.Pack id id η δ B U q Γ A)(U':Grid c): (∑ i:Tick c,pairQ Γ i U')=U U':=by
    apply Sway.whist; intro i j
    ext a b; change (∑ i:Tick c,pairQ Γ i U') (i,a) (j,b)=_; rw [Matrix.sum_apply]; unfold Tick pairQ; simp only [Fintype.sum_prod_type, Stew.block,Matrix.of_apply];
    rw [sum_eq_single i]; rotate_left; · intro x _ hx; simp [hx.symm]
    · simp
    rw [sum_eq_single j]; rotate_left; · intro x _ hx; simp [hx.symm]
    · simp
    simp only [true_and,ite_true, fareP, and_self]; rw [← h.sells, Matrix.sum_apply]
lemma setsK (h:Run.Pack id id η δ B U q Γ A)(U': Grid c)(N:ℕ): (∑ i:Tick c,(sealG Γ N).view i U') = paleF N (U U'):=by
    let f: Equiv.Perm (Tick c):=⟨flopT,flopT,fun _=>rfl,fun _=>rfl⟩
    let L i:=pairQ Γ i U'; change (∑ i:Tick c,nozzle c N (gleam Γ U' i)) = nozzle c N _; rw [← map_sum]; refine congr_arg _ ?_; unfold gleam; rw [← Finset.smul_sum, Finset.sum_add_distrib]; change  (2:ℝ)⁻¹ • ((∑ x:Tick c,L x)+(∑ x:Tick c,L (f x))) = _; rw [show (∑ i:Tick c,L (f i))=∑ i:Tick c,L i from Equiv.sum_comp .., show (∑ i:Tick c,L i) = _ from entriesU h U', ← two_smul ℝ]; exact inv_smul_smul₀ (by norm_num) _
lemma auctions (h:Run.Pack id id η δ B U q Γ A)(hp:0<η)(hc:0≤P){K:ℝ}(hx:∀ X:Support c,tribute B b n X ≤ K*rent 1 B X)(ha:0≤a)(hs:a+1 ≤ δ)(hr:B≤ p.B)(hK:0≤K): Anchored (fun i=>(dispatch i).site) (faceQ A P t B b n) (fun i=>coverNumber p.B (dispatch i).support) a (P*t^2*K*(q+q)):=by
    let f:= faceQ A P t B b n; let g(x):= f x*rent a p.B (dispatch x).support
    have hg x : 0 ≤ g x:=by
       apply mul_nonneg ?_ (fair ..).le; unfold f faceQ; split; next _=> exact mul_nonneg (mul_nonneg (mul_nonneg hc (sq_nonneg t)) (add_nonneg (need h _) (need h _))) (by unfold tribute; positivity)
       next _=> exact le_rfl
    let R (x:Tick c):=P*t^2*K*(Run.rent δ B x.2.2 * silos A x+Run.rent δ B x.2.2 * silos A (flopT x)) -- annotation later
    have he (x:Tick c): g x≤ R x:=by
       unfold R g f faceQ; let X:= x.2.2; let v:=silos A x+silos A (flopT x)
       have hh:0≤v:=add_nonneg (need h _) (need h _);
       rw [← mul_add]; split
       next hf=> rw [show (dispatch x).support=X from if_pos hf]; have hV: Run.rent a p.B X≤ Run.rent a B X:=by unfold Run.rent; apply Real.exp_monotone; gcongr; exact YM.Next.Scheduling.cover_earns hr X
                 rw [mul_assoc (P*t^2*v)]; apply (mul_le_mul_of_nonneg_left (mul_le_mul (hx _) hV (fair ..).le (mul_nonneg hK (fair ..).le)) (show 0≤P*t^2*v by positivity)).trans; rw [mul_assoc K]; unfold Run.rent; rw [← Real.exp_add, ← add_mul]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ((add_comm ..).trans_le hs) (Nat.cast_nonneg _))) hK) (show 0≤P*t^2*v by positivity)).trans_eq; unfold v; ring
       next _=> rw [zero_mul]; exact mul_nonneg (by positivity) (mul_nonneg (fair ..).le hh)
    intro i; refine ⟨fun x=> ?_, Summable.of_finite,?_⟩
    · change 0 ≤ if x.1=i then g x else 0; split; exact hg _; exact le_rfl
    rw [tsum_fintype]; apply (sum_le_sum (g:=fun x:Tick c=> if x.1=i then R x else 0) fun x _=> ?_).trans; rotate_left; · change (if x.1=i then g x else 0)≤_; split <;> first | exact le_rfl | exact he _
    unfold Tick; simp only [Fintype.sum_prod_type]; rw [sum_eq_single i]; rotate_left; · intro x _ hx; simp [hx]
    · simp
    simp only [ite_true]; unfold R; simp only [← mul_sum,silos,sum_add_distrib]; exact mul_le_mul_of_nonneg_left (add_le_add (h.spends i) (h.dues i)) (by positivity)
end YM.QCD.Entr
