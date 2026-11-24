import YM.Bloom.Fruit
/-! # Rates from two-legs FD lifts globally W. Parent transport later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bloom.Jar
open Function Lattice Laurent Bloch Filter Arise YM.Bank Precision
open Jule Metric
open scoped Topology BigOperators
variable {t w k j n m ℓ p r:ℕ}
variable {e b C A:ℝ}
variable {H: Type*}
-- Velocity family.X includes metadata. p.w aperture.DONE
noncomputable def posT (w:ℝ)(n:ℕ)(x:Cover):E4:= (w^n)⁻¹ • Kith.rock x
lemma towards(h:0< n)(x:Cover): Tendsto (fun w:ℝ=> posT w n x) atTop (𝓝 0):=by
   simpa only [posT,zero_smul] using! (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (α:=ℝ) (by omega:n ≠ 0))).smul_const (Kith.rock x)
lemma spread (w:ℝ)(n:ℕ)(x y:Cover): posT w n (x+y)=posT w n x+posT w n y:=by unfold posT; rw [← smul_add]; congr 1; ext a; simp [Kith.rock]
lemma unspread (w:ℝ)(n:ℕ)(x y:Cover):posT w n (x-y)=posT w n x-posT w n y:=by unfold posT; rw [←smul_sub]; congr 1; ext a; simp [Kith.rock]
lemma disc {x:E4}(he:e ≤ ‖x‖)(ht:‖x‖ ≤ b) : x∈Oasis e b:= ⟨by simpa,by simpa [Set.mem_compl_iff]⟩
lemma shelves (h:0<n)(he:0<e)(b:ℝ)(u:Cover):∀ᶠ w:ℝ in atTop,∀ x:Cover,posT w n x∈Oasis e b → posT w n (x+u) ∈ Oasis (e/2) (b+1):=by
      have hp:Tendsto (fun w:ℝ=> ‖posT w n u‖) atTop (𝓝 0):= by simpa only [norm_zero] using (towards h u).norm
      filter_upwards [hp.eventually (gt_mem_nhds (show 0<min (e/2) 1 from lt_min (by positivity) zero_lt_one))] with w hw; have ht:‖posT w n u‖ < min (e/2) 1:=hw; intro x hx; rw [spread]; obtain ⟨hx,hz⟩:= consp hx; apply disc
      · have hQ:= (norm_sub_le (posT w n x+posT w n u) (posT w n u)); rw [add_sub_cancel_right] at hQ; linarith [ht.trans_le (min_le_left ..)]
      exact (norm_add_le ..).trans (add_le_add hz (le_of_lt (ht.trans_le (min_le_right ..))))
structure Peer (H:Type*) where
    w:ℝ
    z:Cover
    f:Side
    x:Cover
    y:Cover
    A:H
-- positions included only after z.
noncomputable def ShelfH (n:ℕ)(e b:ℝ)(G: H→ Side→ Prop): Filter (Peer H):= Filter.bind (atTop:Filter ℝ) fun w=>Filter.bind (𝓟 {z:Cover|posT w n z∈ Oasis e b}) fun z=>Filter.bind (atTop:Filter Side) fun f=> 𝓟 {x| x.w=w∧x.z=z∧x.f=f∧x.x-x.y=z∧G x.A f}
variable {G:H→ Side→Prop}
lemma eaves (P: Peer H→Prop) : (∀ᶠ i in ShelfH n e b G,P i) ↔ ∀ᶠ w:ℝ in atTop,∀ z:Cover,posT w n z∈Oasis e b→∀ᶠ f:Side in atTop,∀ x y A,x-y=z→ G A f→ P ⟨w,z,f,x,y,A⟩:=by
    simp_rw [ShelfH,eventually_bind,eventually_principal,Set.mem_setOf_eq]; apply Filter.eventually_congr; apply Eventually.of_forall; intro w
    refine forall_congr' fun z=> imp_congr_right fun h=> Filter.eventually_congr (Eventually.of_forall fun f=>?_); constructor
    · intro h x y a hp ht; exact h _ ⟨rfl,rfl,rfl,hp,ht⟩
    · rintro h ⟨w,z,f,x,y,a⟩ ⟨rfl,rfl,rfl,hp,ht⟩; exact h x y a hp ht
-- core generic: K bil Paar. canonical strikes have limit for all l1 and l2, plus directions le etc. first separate cost when poses off-center. general at H.
variable (K: Side→H→ Cover→Cover→Parc→Parc→ℂ)
variable (L : Side→H→Cover→Cover→Parc→Parc→ₗ[ℝ]ℂ) (R : Side→H→Cover→Cover→Parc→Parc→ₗ[ℝ]ℂ)
-- syrup: ∀ᶠ ... if u v inside compact.J.Pay with scales.Span. 
def Vows (G:H→Side→Prop) (T:List Axis→List Axis→E4→ℂ) (N:ℕ)(t:ℕ)(p r:ℕ): Prop := ∀ (l u : List Axis),l.length≤ p→u.length≤ r→∀ (v y:Cover)(b e:ℝ), 0<e → ∃ C:ℝ,0≤ C∧∀ᶠ i in ShelfH N e b G,
     i.w*‖(i.w^N)^(t+l.length+u.length) • K i.f i.A i.x i.y (strike l v) (strike u y) - T l u (posT i.w N (i.z+(v-y)))‖ ≤ C -- shifted target guaranteed
section vow
variable {T:List Axis→List Axis→ E4→ℂ}
lemma raises (hk: Vows K G T n t p r)(hn:0<n)(l y:List Axis)(u v:Cover)(hl:l.length≤p)(hr:y.length≤r)(hp:∀ z:E4, z ≠0→ ContinuousAt (T l y) z)(he:0<e)(b:ℝ)(ht:m ≤ t+l.length+y.length) : ∃ C: ℝ, 0 ≤ C ∧∀ᶠ i in ShelfH n e b G, ‖ K i.f i.A i.x i.y (strike l u) (strike y v)‖ ≤ C*((i.w^n)^m)⁻¹:=by
     let F:=ShelfH n e b G; let M:= t+l.length+y.length; let f:= T l y; let O:= Oasis (e/2) (b+1); let κ:=fun i:Peer H=> K i.f i.A i.x i.y (strike l u) (strike y v); let z:=fun i:Peer H=> i.z+(u-v)
     obtain ⟨C,hc,H⟩:= hk l y hl hr u v b e he
     have hv : IsCompact O:= (isCompact_closedBall ..).inter_right (isOpen_ball.isClosed_compl)
     obtain ⟨D,hD⟩ := hv.bddAbove_image (fun x (hx:x∈O)=> ((hp x (door hx (by positivity))).norm).continuousWithinAt) -- hp Continu not .continuousAt
     let Y:= max D 0; have hy:0 ≤ Y:=le_max_right ..
     have hE: ∀ᶠ i in F,posT i.w n (z i) ∈ O:=by rw [eaves]; filter_upwards [shelves hn he b (u-v)] with w hw z' h; exact Eventually.of_forall fun c x y A _ _=>hw _ h
     have hU : ∀ᶠ i in F, 1 ≤ i.w :=by rw [eaves]; filter_upwards [eventually_ge_atTop (1:ℝ)] with w hw z _; exact Eventually.of_forall fun c x y A _ _=>hw
     refine ⟨C+Y,add_nonneg hc hy, ?_⟩; filter_upwards [hE,hU,H] with i hE hU hT
     let V:= posT i.w n (z i); have hq : ‖f V‖≤ Y:= le_trans (hD (Set.mem_image_of_mem _ hE)) (le_max_left ..)
     let X:= i.w^n; have hx:1 ≤ X:=one_le_pow₀ hU; have hs:=zero_lt_one.trans_le hx
     rw [← div_eq_mul_inv,le_div_iff₀ (pow_pos (show 0 < i.w^n from hs) _),mul_comm]; apply (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hx ht) (norm_nonneg _)).trans
     let U:= X^M • κ i; rw [show X^M * ‖κ i‖= ‖U‖ from (by rw [show ‖U‖= ‖X^M‖ * ‖κ i‖ from norm_smul ..,Real.norm_of_nonneg (by positivity)])]; apply (norm_le_norm_sub_add _ _).trans (add_le_add ?_ hq)
     exact (le_mul_of_one_le_left (norm_nonneg _) hU).trans hT
-- two-ledges. track budget all positions. no Ne.P.
lemma pontoons (hL:∀ f m x y X Y,L f m x y X Y=K f m x y Y X) (hR:∀ f m x y X Y,R f m x y X Y=K f m x y X Y) (hk:Vows K G T n t p r)(hn:0<n)(he:0<e)(b:ℝ) (ho:∀ l u z,l.length ≤ p→u.length≤ r→ z≠0→ ContinuousAt (T l u) z)(X Y: Parc)(hx:X∈tails m p)(hy:Y∈ tails ℓ r) :∃ C:ℝ, 0≤ C∧∀ᶠ i in ShelfH n e b G, ‖K i.f i.A i.x i.y X Y‖ ≤ C*((i.w^n)^(t+m+ℓ))⁻¹:=by
    let F:=ShelfH n e b G; let w:=fun i:Peer H=>((i.w^n)^(t+m+ℓ))⁻¹
    refine Span.payments w F (fun i=>K i.f i.A i.x i.y) (fun i=> L i.f i.A i.x i.y) (fun i=> R i.f i.A i.x i.y) (fun i _ _=>hL ..) (fun i _ _=> hR ..) ?_ (fun a ha ha' x s hs hs' y=> raises K hk hn a s x y ha' hs' (fun i Hi=> ho _ _ i ha' hs' Hi) he b (by omega)) X hx Y hy
    rw [eaves]; filter_upwards [eventually_ge_atTop (1:ℝ)] with p hp z _; exact Eventually.of_forall fun c x y A _ _=> inv_nonneg.mpr (pow_nonneg (pow_nonneg (zero_le_one.trans hp) _) _)
variable (W:List Axis) (J: List Axis)
lemma shelfFunds (hL:∀ f m x y X Y,L f m x y X Y=K f m x y Y X) (hR:∀ f m x y X Y,R f m x y X Y=K f m x y X Y) (hk:Vows K G T n t (p+1) (r+1))(hn:0<n)(he:0<e)(b:ℝ) (ho:∀ l u z,l.length ≤ p+1→u.length≤ r+1→ z≠0→ ContinuousAt (T l u) z)(hp:W.length≤ p)(hr:J.length≤r) (X Y:Parc)(i v:Option PlaqAxes)(hx:Rocky i W p X)(hy:Rocky v J r Y): ∃ C:ℝ, 0≤ C∧∀ᶠ a in ShelfH n e b G, a.w*‖(a.w^n)^(t+W.length+J.length) • K a.f a.A a.x a.y X Y - T W J (posT a.w n a.z)‖ ≤ C:=by
    let F:=ShelfH n e b G; let m:= t+W.length+J.length; let X':=strike W 0; let Y':= strike J 0
    obtain ⟨C,hc,H⟩:= hk W J (Nat.le_succ_of_le hp) (Nat.le_succ_of_le hr) 0 0 b e he
    obtain ⟨C',hc',H'⟩:= pontoons K L R hL hR hk hn he b ho _ Y hx.rest (recovered v J r Y hr hy) -- hp implicit?
    obtain ⟨D,hD,HT⟩:= pontoons K L R hL hR hk hn he b ho X' _ (show X'∈ tails W.length (p+1) from Submodule.subset_span ⟨W,0,le_rfl,Nat.le_succ_of_le hp,rfl⟩) hy.rest
    have hQ : ∀ᶠ i in F, 1 ≤ i.w:=by rw [eaves]; filter_upwards [eventually_ge_atTop (1:ℝ)] with w hw z _; exact Eventually.of_forall fun c x y A _ _=>hw
    refine ⟨C'+D+C,by positivity,?_⟩; filter_upwards [hQ,H',H,HT] with a hq h' h ht; let V:=K a.f a.A a.x a.y; let z:=posT a.w n a.z; let R₀:=a.w^n; let T':=T W J z
    have HR : a.w ≤ R₀:= by unfold R₀; exact (by nth_rw 1 [← pow_one a.w]; gcongr; exact hn)
    have h0:=zero_lt_one.trans_le hq; have hV:=h0.trans_le HR
    have he(g:ℂ)(s:ℝ)(hs:‖g‖ ≤ s*(R₀^(m+1))⁻¹): a.w*‖R₀^m • g‖≤s:=by
          refine (mul_le_mul_of_nonneg_right HR (norm_nonneg _)).trans ?_
          rw [norm_smul,Real.norm_of_nonneg (pow_nonneg hV.le _),←mul_assoc, ← pow_succ']; rw [← div_eq_mul_inv,le_div_iff₀ (pow_pos hV _),mul_comm] at hs; exact hs
    rw [sub_self,add_zero] at h
    have hu: K a.f a.A a.x a.y X Y = (V (X-X') Y + V X' (Y-Y'))+ V X' Y':=by unfold V; rw [← hL a.f a.A a.x a.y Y (X-X'),← hR a.f a.A a.x a.y X' (Y-Y'),map_sub,map_sub,hL, hL,hR,hR]; abel
    rw [hu,smul_add,smul_add,add_sub_assoc]; apply (mul_le_mul_of_nonneg_left (norm_add_le ..) h0.le).trans; rw [mul_add]; refine add_le_add ?_ h; apply (mul_le_mul_of_nonneg_left (norm_add_le ..) h0.le).trans; rw [mul_add]; refine add_le_add (he _ _ ?_) (he _ _ ?_)
    · exact (h'.trans_eq (by rw [show t+(W.length+1)+J.length=m+1 by unfold m; omega]))
    exact ht
end vow
end YM.Bloom.Jar
#print axioms YM.Bloom.Jar.shelfFunds
