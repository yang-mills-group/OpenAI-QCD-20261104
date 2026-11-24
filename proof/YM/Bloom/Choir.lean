import YM.Bloom.Cilium
/-! # absolute halo exposures: widths cut plus closeness.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bloom.TreeP
open Function Lattice Laurent Bloch Metric RG Filter
open Finset YM.Bank Precision Matrix Exterior Arise Arise.Range Jar
open YM.Bank.Jule Ivo Pic Maxwell Hypnos Hypnos.Fruit
open AnalyticBridge.LocalGaussianLaws.Current FreeResolvent
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {G:Gauge}{c f:Side}{k m n j b B q r:ℕ}{X Y Z:Type}
-- scalar D
noncomputable def fareV (G:Gauge)(d v:ℕ):ℝ:= ((v+v+1)^4*Fintype.card (PAC G d):ℕ)
lemma duster(x:Site c)(p:PlaqAxes)(e: Body 1 c) (m: Body 1 c→ℝ)(h:m=Pi.single e 1) : d 1 c (x,plaquette p) e=m (x+step p.val.1,coord p.val.2)-m (x,coord p.val.2) - (m (x+step p.val.2,coord p.val.1)-m (x,coord p.val.1)):=by
      rw [← d_plaquettes,h]; simp [mulVec,dotProduct,Pi.single_apply,mul_ite] -- remove
lemma d_one (x:Col G c) (i:FreeResolvent.Slot G c 1) (h:radi G c x i≠0): i∈clique G c 1 1 x.1:=by
     rcases x with ⟨x,p,a⟩; obtain ⟨p,rfl⟩:= plaqEquiv.surjective p; obtain ⟨i,j,b⟩:= i; let t:TypeFace 2:=plaqEquiv p; change ↑(if a=b then d 1 c (x,t) (i,j) else (0:ℝ))≠ (0:ℂ) at h; split_ifs at h with he; swap; · simp at h
     have ht : i=x ∨ i=x+step p.val.1 ∨ i=x+step p.val.2:=by
        by_contra hk; push Not at hk; obtain ⟨h₁,h₂,h₃⟩:=hk; apply h; change (↑(d 1 c (x,plaquette p) (i,j)):ℂ)=_; rw [duster x p (i,j) _ rfl]; simp [Pi.single_apply,Ne.symm h₁,Ne.symm h₂,Ne.symm h₃]
     refine clique_ion ..|>.2 (halo_spec.mpr ⟨x,mem_singleton_self x,?_⟩); rcases ht with rfl|rfl|rfl; · simp
     · exact Work.E03.sep_step ..
     exact Work.E03.sep_step ..
lemma d_ear (x:Col G c)(i:FreeResolvent.Slot G c 1) : ‖radi G c x i‖≤4:=by
    rcases x with ⟨x,p,a⟩; obtain ⟨p,hp⟩:= plaqEquiv.surjective p; rw [← hp]; obtain ⟨i,j,b⟩:=i; unfold radi paid; rw [Matrix.map_apply,Complex.norm_real]; change ‖(if a=b then d 1 c (x,plaquette p) (i,j) else (0:ℝ))‖ ≤ _; split_ifs; swap; · simp
    rw [duster x p (i,j) _ rfl]; let F:= (Pi.single (i,j) 1: Exterior.form 1 c)
    have he (p:Body 1 c) : ‖F p‖≤1:=by unfold F; rw [Pi.single_apply]; split <;> simp
    exact (norm_sub_le ..).trans ((add_le_add (norm_sub_le ..) (norm_sub_le ..)).trans ((add_le_add (add_le_add (he _) (he _)) (add_le_add (he _) (he _))).trans_eq (by norm_num)))
lemma d_cusp (x:Col G c) : cusp (radi G c) x ≤ fareV G 1 1 * 4:= (cupful _ (clique G c 1 1 x.1) _ _ (d_ear x) (d_one x)).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (clique_cost ..)) (by norm_num))
-- real stealth.P paid normal tensor
variable (P: Parc)
noncomputable def flet (P:Parc):ℕ:=P.support.sup Laurent.size
noncomputable def pattern (P: Parc):ℝ:=∑ i∈ P.support, ‖P i‖
lemma valor_g (P:Parc): 0 ≤ pattern P:= sum_nonneg (fun _ _=>norm_nonneg _)
lemma marchO (c:Side)(u x:Cover)(h:u ∈ P.support) (hb:flet P ≤ b):wrap c (x+u)∈halo b {wrap c x}:=by
    refine halo_spec.mpr ⟨_,mem_singleton_self _,?_⟩; rw [separation_comm,separation,map_add,add_sub_cancel_left]; exact (Next.Free.within_size ..).trans ((le_sup (s:=P.support) (f:=Laurent.size) h).trans hb) -- namespace
variable (x:Cover)(i:G.ColorIndex)(p:PlaqAxes)
noncomputable def pupil (G:Gauge)(c:Side)(x:Cover)(p:PlaqAxes)(i:G.ColorIndex)(P:Parc): Matrix Unit (Col G c) ℂ:=lavish c i 2 (stalk c x (plaquette p) P)
lemma stays0 (z:Col G c)(hz:pupil G c x p i P () z≠0)(hp:flet P ≤ b): z∈ clique G c 2 b (wrap c x):=by
     unfold pupil lavish at hz; rw [of_apply] at hz; split at hz; swap; · simp_all
     rw [taught] at hz; unfold Arise.sound at hz; rw [Finsupp.linearCombination_apply] at hz; obtain ⟨a,ha,h⟩:= Finset.exists_ne_zero_of_sum_ne_zero (fun H=> hz ((Complex.ofReal_eq_zero).2 H)) -- h implicit
     dsimp only at h; split at h; next he => rw[clique_ion,← congr_arg Prod.fst he]; exact marchO P c a x ha hp
     next=> simp at h
lemma cusp_pupil (z:Col G c) : ‖pupil G c x p i P () z‖ ≤ pattern P:=by
     unfold pupil lavish; rw [Matrix.of_apply]; split; swap; · rw [norm_zero]; exact valor_g P
     rw [Complex.norm_real,taught]; unfold Arise.sound; simp only [Finsupp.linearCombination_apply,Finsupp.sum]; refine (norm_sum_le ..).trans (sum_le_sum (fun j _=>?_)); split <;> simp
lemma purse0 : cusp (pupil G c x p i P) () ≤ fareV G 2 (flet P)*pattern P:= (cupful _ _ _ _ (cusp_pupil P x i p) (fun i h=>stays0 P x _ p i h (show flet P ≤ flet P from le_rfl))).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (clique_cost ..)) (valor_g P))
variable (o: Site c)
lemma d_stir (R: Matrix (Col G f) (Col G c) ℂ)(hp:flet P ≤ b)(hr:∀ u∈clique G f 2 b (wrap f x),∀ v,R u v≠0→ v∈clique G c 2 B o) (v:FreeResolvent.Slot G c 1) (hh:(pupil G f x p i P*R*radi G c) () v≠0): v∈ clique G c 1 (B+1) o:=by
     rw [Matrix.mul_apply] at hh; obtain ⟨u,hu,h⟩:= Finset.exists_ne_zero_of_sum_ne_zero hh; have hx:=right_ne_zero_of_mul h; have hy:=left_ne_zero_of_mul h
     rw [Matrix.mul_apply] at hy; obtain ⟨t,ht,h'⟩:= Finset.exists_ne_zero_of_sum_ne_zero hy; have ha:= hr t (stays0 _ _ _ _ _ (left_ne_zero_of_mul h') hp) u (right_ne_zero_of_mul h')
     obtain ⟨m,hm,H⟩:= halo_spec.mp ((clique_ion ..).mp ha); obtain ⟨w,hw,HV⟩:= halo_spec.mp ((clique_ion ..).mp (d_one u v hx)); rw [mem_singleton.mp hw] at HV; exact clique_ion ..|>.2 (halo_spec.mpr ⟨m,hm,(separation_triangle ..).trans (Nat.add_le_add H HV)⟩)
variable {a d s:ℝ}(g:Ratio c f)(J: Matrix (Exterior.Body 2 f) (Exterior.Body 2 c) ℝ)(F H:Bed)
-- tensor real over genuine.J.
lemma hourly (c f k r B:ℕ)(n m l: Side) (J:Matrix (Exterior.Body k n) (Exterior.Body r m) ℝ)(B':Matrix (Exterior.Body r m) (Exterior.Body B l) ℝ): paid G (J*B')= paid G J*paid G B':=by unfold paid; rw [AnalyticBridge.LocalGaussianLaws.Current.tensor_mul]; exact Bloch.prom_mul ..
lemma billable (ha:0 < a)(hb:0 ≤ d)(ht:P∈tails k n)(hj:n+2≤j):∃ C:ℝ,0≤ C ∧∀ {c f:Side}(x:Cover)(p:PlaqAxes)(i:G.ColorIndex) (g:Ratio c f)(J:Matrix (Exterior.Body 2 f) (Exterior.Body 2 c) ℝ)(F H:Bed), Fare j a d g J F H→∀ z:FreeResolvent.Slot G c 1, ‖(pupil G f x p i P*paid G J*radi G c) () z‖ ≤ C/(g.count.val:ℝ)^(2+k):=by
     obtain ⟨C,hc,h⟩:=priced P hj ht ha hb; refine ⟨C,hc,fun {c f} x p i g J F H h' z=>?_⟩; rw [Matrix.mul_assoc,show paid G J*radi G c= _ from (hourly 0 0 2 2 1 f c c J (Exterior.d 1 c)).symm,pupil,churn,lavish,Matrix.of_apply]; split; · rw [Complex.norm_real]; apply h _ _ _ _ h'
     rw [norm_zero]; positivity
-- cut.ALL.T.L1 true only
open AnalyticBridge.LocalGaussianLaws
lemma profuse (hp:flet P ≤ b)(ht:0 ≤ s)(hz:∀ v:FreeResolvent.Slot G c 1,‖(pupil G f x p i P*paid G J*radi G c) () v‖ ≤ s)(R : Matrix (Col G f) (Col G c) ℂ) (hr:∀ u∈ clique G f 2 b (wrap f x),∀ v,R u v ≠0 → v∈clique G c 2 B o)(hv:∀ z: Col G f,cusp (paid G J-R) z ≤ a) (ha:0≤ a):
     let K:=pupil G f x p i P; let α:=fareV G 2 (flet P)*pattern P*a*(fareV G 1 1*4); cusp (K*paid G J*radi G c) () ≤ α+fareV G 1 (B+1)*(α+s):=by
       intro K α
       let β:=fareV G 1 1*4; let Z:= fareV G 2 (flet P)*pattern P; have he : 0 ≤ β:= by unfold β fareV; positivity
       have hy:= (purse0 (G:=G) P (c:=f) x i p); have hk: 0 ≤ Z:= (cups_pos K ()).trans hy
       let U:= K*R*radi G c; apply cup_diff _ U s α _ _ ht (show 0≤ Z*a*β from by positivity) (Nat.cast_le.mpr (clique_cost o)) () hz ?_ (d_stir P x i p o R hp hr)
       unfold U; rw [← Matrix.sub_mul,← Matrix.mul_sub]; exact cups_tender _ _ _ _ he () (cups_tender _ _ _ _ ha () hy hv) d_cusp -- syntax
end YM.Bloom.TreeP
#print axioms YM.Bloom.TreeP.billable
#print axioms YM.Bloom.TreeP.profuse
