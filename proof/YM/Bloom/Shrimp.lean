import YM.Bloom.Toil
/-! # weighted contributions spice. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bloom.Buzz
open Function Lattice Laurent Bloch Metric RG Filter Arise Arise.Range Massive UV UV.Free
open Finset YM.Bank Precision Matrix YM.Bloom
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Classical
open QCD QCD.Lat QCD.Free QCD.Flume QCD.Bank Next.Free YM.Bloom.TreeP
open QCD.Creek QCD.Anomaly QCD.Cove QCD.Grass
open YM.Bank.Jule YM.Bank.Pic YM.Bloom.Jar
variable {c f:Side}{k m j B r L n D d E:ℕ}{a b u v t s W ε C S A:ℝ}
variable (p:Sings k)(q:Sings m)(x y:Cover)
noncomputable def spig (W:ℝ)(p:Sings k):ℝ:=W^(3+2*order_p p)
noncomputable def splice (W:ℝ)(c: Side)(p:Sings k)(x:Cover): Matrix Unit (Keys c 6) ℂ := (spig W p:ℂ) • tokenS c p x
lemma wheel_pair (J: Matrix (Keys f 6) (Keys f 6) ℂ) : splice (W^n) f p x*J*(splice (W^n) f q y).transpose= (W^(2*n))^(3+order_p p+ order_p q) • (tokenS f p x*J*(tokenS f q y).transpose):=by
     unfold splice; rw [Matrix.smul_mul,Matrix.smul_mul, Matrix.transpose_smul,Matrix.mul_smul]; -- order check
     rw [show (W^(2*n):ℝ)= (W^n)^2 from by rw [mul_comm,pow_mul],show ((W^n)^2:ℝ)^(3+order_p p+order_p q)= (spig (W^n) p)*(spig (W^n) q) from ?_]; · ext; simp only [Matrix.smul_apply,Complex.real_smul,Complex.ofReal_mul,smul_eq_mul,mul_assoc] -- order
     unfold spig; rw [←pow_add,←pow_mul]; congr 1; omega
structure Tropic (D n j:ℕ)(ε s C W:ℝ)(f:Side): Prop where
     title k(h:k ≤ D)m(ht:m ≤ D)(p:Sings k)(q:Sings m)(x y:Cover)(F:Train j)(hp:posT W (2*n) (x-y)∈Oasis ε s): ‖(splice (W^n) f p x*start f F 6*(splice (W^n) f q y).transpose) () ()-pin p q (posT W (2*n) x) (posT W (2*n) y)‖ ≤ C/W
variable (h:Spar D L (2*n) j ε s C)
lemma peps (hp:k ≤ D)(ht:1≤ W):0 ≤ spig W p ∧ spig W p ≤ billN W D:= ⟨pow_nonneg (zero_le_one.trans ht) _,pow_le_pow_right₀ ht (by have hv:order_p p ≤ D:= (measures p).trans hp; omega)⟩
include h
lemma smells :∀ᶠ W:ℝ in atTop,∀ᶠ c:Side in atTop,Tropic D n j ε s C W c:=by
     let P:=fun k m (p:Sings k)(q:Sings m)(W:ℝ)(c:Side)=> ∀ z:Cover,posT W (2*n) z∈Oasis ε s →∀ x y:Cover,x-y=z→∀ F:Train j,W*‖ (W^(2*n))^(3+order_p p+order_p q) • (tokenS c p x*start c F 6*(tokenS c q y).transpose) () ()-pin p q (posT W (2*n) x) (posT W (2*n) y)‖ ≤ C
     have hp:= eachH atTop D (fun k m p q W=>∀ᶠ c in atTop,P k m p q W c) (fun _=>inferInstance) (fun i hi j hj p q=>booths _ (h.compare i hi j hj p q)); filter_upwards [hp,eventually_gt_atTop (0:ℝ)] with W hw ha; filter_upwards [eachH atTop D (fun k m p q=>P k m p q W) (fun _=> inferInstance) hw] with c hc
     constructor; intro k hk m hm p q x y F ht; rw [wheel_pair, Matrix.smul_apply,le_div_iff₀ ha,mul_comm]; exact hc k hk m hm p q (x-y) ht x y rfl F
lemma packed (ht:1 ≤ W)(hk:k ≤ D): cusp (splice W c p x) () ≤ billN W D*C:=by unfold splice; rw [cups_scale,Complex.norm_real,Real.norm_of_nonneg (peps p hk ht).1]; exact mul_le_mul (peps p hk ht).2 ((startsU p x).trans (h.price _ hk p)) (cups_pos ..) ((peps p hk ht).1.trans (peps p hk ht).2)
lemma locked (hp:k ≤ D)(hv:L ≤ B)(i:Keys c 6) (he: splice W c p x () i≠0):i∈ limits (halo B {wrap c x}):=by unfold splice at he; rw [Matrix.smul_apply,smul_eq_mul] at he; exact paint_zone _ _ _ _ _ _ (right_ne_zero_of_mul he) ((h.span _ hp p).trans hv)
lemma settled(F:Train j)(hp:k≤D)(ht:m ≤ D)(hw:1≤ W): ‖(splice W f p x*start f F 6*(splice W f q y).transpose) () ()‖ ≤ billN W D*(billN W D*C):=by
     unfold splice; rw [Matrix.smul_mul,Matrix.smul_mul,Matrix.transpose_smul,Matrix.mul_smul,Matrix.smul_apply,Matrix.smul_apply,norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (peps q ht hw).1,Real.norm_of_nonneg (peps p hp hw).1]; have hx:0 ≤ billN W D:=pow_nonneg (zero_le_one.trans hw) _; exact mul_le_mul (peps p hp hw).2 (mul_le_mul (peps q ht hw).2 (h.youth k hp m ht p q f F x y) (norm_nonneg _) hx) (mul_nonneg (peps q ht hw).1 (norm_nonneg _)) hx
variable (g: Ratio c f) (F H:Train j){U X Q}(hG:Giant j g F H U X Q)
structure Porter (t:ℝ)(D:ℕ)(c:Side)(e:ℝ): Prop where
     meter: 1 ≤ t
     earn : 0 ≤ e
     price k(hk:k≤ D): t^(3+2*k)*gear c k ≤ e
include hG
variable (hT: Porter W D g.count A)
include hT
lemma spliced (x:Cover)(y:Cover)(hp:k ≤ D)(hq:m ≤ D): ‖(splice W f p x *lowT H (Buzz.wheel U X 6)*(splice W f q y).transpose) () ()‖ ≤ C*A^2:=by
     unfold splice; let P:= spig W p; let Q:= spig W q; let u:=gear g.count (order_p p); let v:= gear g.count (order_p q); have ht:0≤ P:= (peps p hp hT.meter).1; have he:0 ≤ Q:= (peps q hq hT.meter).1
     rw [Matrix.smul_mul,Matrix.smul_mul,Matrix.transpose_smul,Matrix.mul_smul,Matrix.smul_apply,Matrix.smul_apply,norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg ht,Real.norm_of_nonneg he]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h.pearly k hp m hq p q g F H hG x y) he) ht).trans
     change P*(Q*(C*(u*v))) ≤ _; rw [show P*(Q*(C*(u*v)))= C*((P*u)*(Q*v)) from by ring,sq]; exact mul_le_mul_of_nonneg_left (mul_le_mul (hT.price (order_p p) ((measures p).trans hp)) (hT.price (order_p q) ((measures q).trans hq)) (mul_nonneg he (gear_pos ..).le) hT.earn) h.pay.le
noncomputable def pocketV (W C T A:ℝ)(D B:ℕ):= let α:= billN W D*(C*T); α+ audit B 6*(α+C*A)
lemma taking (w:Site c)(hp:k ≤ D)(hv:L ≤ E)(R:Matrix (Keys f 6) (Keys c 6) ℂ)(he:∀ i∈ limits (F:=6) (halo E {wrap f x}),∀ j,R i j ≠0 → j∈limits (halo B {w}))(hs:∀ i,cusp (Buzz.wheel U X 6-R) i ≤ S)(hz:0≤ S): cusp (splice W f p x*Buzz.wheel U X 6) () ≤ pocketV W C S A D B:=by
     let P:= spig W p; let α:=tokenS f p x; have ht:= peps p hp hT.meter; have hw:0 ≤ P:=ht.1; let β:=sur p; let Y:= billN W D*(C*S); let j':= audit B 6; have hZ:0 ≤ j':=by unfold j' audit; positivity
     let V:=gear g.count (order_p p); have hh:0 ≤ C*V:=mul_nonneg h.pay.le (gear_pos ..).le
     have ha : cusp (α*Buzz.wheel U X 6) () ≤ β*S+j'*(β*S+C*V):=valves_full _ _ _ _ _ _ _ w ((h.span _ hp p).trans hv) _ he (h.ask k hp p g F H hG x) hs hh hz
     unfold splice; rw [Matrix.smul_mul,cups_scale,Complex.norm_real,Real.norm_of_nonneg hw]; apply (mul_le_mul_of_nonneg_left ha hw).trans; have hg:P*(β*S) ≤ Y := mul_le_mul ht.2 (mul_le_mul_of_nonneg_right (h.price _ hp p) hz) (mul_nonneg (solemn _) hz) (ht.1.trans ht.2)
     have H: P*(C*V)≤ C*A:=by rw [mul_left_comm P]; exact mul_le_mul_of_nonneg_left (hT.price _ ((measures p).trans hp)) h.pay.le
     rw [show P*(β*S+j'*(β*S+C*V))= P*(β*S)+j'*(P*(β*S)+P*(C*V)) from by ring]; exact add_le_add hg (mul_le_mul_of_nonneg_left (add_le_add hg H) hZ)
end YM.QCD.Bloom.Buzz
#print axioms YM.QCD.Bloom.Buzz.settled
#print axioms YM.QCD.Bloom.Buzz.taking
#print axioms YM.QCD.Bloom.Buzz.smells
