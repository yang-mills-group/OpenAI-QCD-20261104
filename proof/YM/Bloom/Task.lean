import YM.Bloom.Ink
/-! # gauge budget input native all.Patch-phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bloom
open Function Lattice Laurent Bloch Metric RG Filter
open Finset YM.Bank Precision Matrix Exterior Arise Arise.Range Jar
open YM.Bank.Jule Ivo Pic Maxwell Hypnos Hypnos.Fruit TreeP
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {G:Gauge}{c f:Side}{k m j B r L n D d:ℕ}{a b u v t s W ε C:ℝ}
structure Eyes (G:Gauge)(D L n j:ℕ) (a v b ε s C:ℝ): Prop where
    pay :0 < C
    span k(h:k ≤ D)(p: Zinc G k) : flet (glimpse p) ≤ L
    price k(h:k ≤ D)(p:Zinc G k): tollP p ≤ C
    youth k(h:k ≤ D) m(ht:m ≤ D)(p:Zinc G k)(q:Zinc G m) (f:Side) (F:Bed) (hx:Grain a v b F f)(x y:Cover) : ‖pop1 (voteP f p x) (voteP f q y) (heartP F G f) () ()‖ ≤ C
    ask k(h:k ≤ D)(p:Zinc G k){c f:Side} (g:Ratio c f) (J:Matrix (Body 2 f) (Body 2 c) ℝ)(F H:Bed)(ht:Fare j a b g J F H)(x:Cover)(z:FreeResolvent.Slot G c 1): ‖(voteP f p x*paid G J*radi G c) () z‖≤ C/(g.count.val:ℝ)^(2+(stemP p).length)
    pearly k (h:k ≤ D) m(ht:m ≤ D)(p:Zinc G k)(q:Zinc G m){c f:Side}(g:Ratio c f) (J: Matrix (Body 2 f) (Body 2 c) ℝ)(F H:Bed) (ht:Fare j a b g J F H)(x y:Cover) : ‖pop1 (voteP f p x) (voteP f q y) (treasureP f c G H (paid G J)) () ()‖ ≤ C/(g.count.val:ℝ)^(4+(stemP p).length+(stemP q).length)
    sense k(h:k≤ D) m(ht:m ≤ D)(p:Zinc G k)(q:Zinc G m) (x:E4) (hx:x∈Oasis ε s): ‖viewK p q x‖ ≤ C
    compare k(h:k ≤ D) m(h':m ≤ D)(p:Zinc G k)(q:Zinc G m): ∀ᶠ W:ℝ in atTop,∀ z:Cover,posT W n z∈Oasis ε s →∀ᶠ f:Side in atTop,∀ x y:Cover,∀ F:Bed,x-y=z→ Grain a v b F f → W*‖ (W^n)^(4+(stemP p).length+(stemP q).length) • pop1 (voteP f p x) (voteP f q y) (heartP F G f) () () - viewK p q (posT W n z)‖ ≤ C
-- Binder risk arrow unknown. receipt.
variable (ha:0<a)(hv:0<v)(hb:0 ≤ b) (hn:10+2*D≤ n)(hj:D+3≤ j)(he:0<ε)(s:ℝ)
set_option maxHeartbeats 1000000 in
lemma extendsP (G:Gauge)(D:ℕ):∃ L:ℕ,∀ k ≤ D,∀ p:Zinc G k, flet (glimpse p)≤ L:=by
    let W(k:ℕ): ℕ:=univ.sup fun p:Zinc G k=>flet (glimpse p); refine ⟨(Finset.range (D+1)).sup W,?_⟩; intro k hk p; have h:flet (glimpse p) ≤ W k:=Finset.le_sup (f:=fun v:Zinc G k=>flet (glimpse v)) (mem_univ p); exact h.trans (le_sup (f:=W) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
variable (E:∀ k ≤ D,∀ p:Zinc G k, flet (glimpse p)≤ L)
include he
lemma tepid (G:Gauge)(p: Zinc G k)(q:Zinc G m): ContinuousOn (viewK p q) (Oasis ε s):=by -- need include he
     intro x hx; let l:=stemP p; let u:=stemP q; have h':x∈away:=door hx he
     have hp : viewK p q=ᶠ[𝓝 x] (if p.2=q.2 then stove (from_p p.1.2.1 q.1.2.1) l u else 0):=by
          filter_upwards [open_away.mem_nhds h'] with y hy; rw [vicar]; have hv:=Arise.Range.gaugeWet y 0 p.1.2.1 p.2 l q.1.2.1 q.2 u hy; rw [sub_zero] at hv; rw [hv]; split <;> simp_all
     have hT : ContinuousAt (viewK p q) x:= ContinuousAt.congr (?_) hp.symm -- hp orientation?
     exact hT.continuousWithinAt
     split; · exact stipend _ _ _ _ x h'
     exact continuousAt_const
include E ha hv hb hn hj he
lemma earns : ∃ C:ℝ, Eyes G D L n j a v b ε s C:=by
     let hY(k m:ℕ)(p: Zinc G k)(q: Zinc G m)(C:ℝ) := ∀ (f:Side)(F:Bed), Grain a v b F f→∀ x y:Cover, ‖pop1 (voteP f p x) (voteP f q y) (heartP F G f) () ()‖ ≤ C
     obtain ⟨Y,hy,H⟩:=pairBill (D:=D) hY (fun i=>inferInstance) (fun k hk m hm p q=>by obtain ⟨C,hc,h⟩:=paid_full (G:=G) (glimpse p) (glimpse q) (laid p) (laid q) ha hb; exact ⟨C,hc,fun f F ht x y=>h f x y _ _ _ _ _ _ ht hv⟩) (fun i _ j _ x y u v hu hv f F h a b=>(hu f F h a b).trans hv)
     let Kg (k:ℕ)(p: Zinc G k)(C:ℝ):=∀ {c f:Side}(g: Ratio c f)(J:Matrix (Body 2 f) (Body 2 c) ℝ)(F H:Bed)(ht:Fare j a b g J F H)(x:Cover)(z:FreeResolvent.Slot G c 1), ‖(voteP f p x*paid G J*radi G c) () z‖ ≤ C/(g.count.val:ℝ)^(2+(stemP p).length)
     obtain ⟨M,hM,HM⟩:= firstP (D:=D) Kg (fun _=>inferInstance) (fun k hk p=>by obtain ⟨C,hc,h⟩:= billable (G:=G) (glimpse p) ha hb (laid p) (by omega:(k+1)+2≤j); exact ⟨_,hc,fun {c f} g J F H ht x z=>h x _ _ g J F H ht z⟩) (fun i _ p u v h hv {c f} g J F H ht x z=> (h g J F H ht x z).trans (div_le_div_of_nonneg_right hv (by positivity)))
     let Jg (k m:ℕ)(p:Zinc G k)(q:Zinc G m)(C:ℝ) := ∀ {c f:Side}(g:Ratio c f)(J:Matrix (Body 2 f) (Body 2 c) ℝ)(F H:Bed)(ht:Fare j a b g J F H)(x y: Cover), ‖pop1 (voteP f p x) (voteP f q y) (treasureP f c G H (paid G J)) () ()‖ ≤ C/(g.count.val:ℝ)^(4+(stemP p).length+(stemP q).length)
     obtain ⟨P,hP,HP⟩:=pairBill (D:=D) Jg (fun _=>inferInstance) (fun k hk m hm p q=>by obtain ⟨C,hc,h⟩:= paid_low (G:=G) (glimpse p) (glimpse q) (laid p) (laid q) (by omega:k+1+2 ≤j) (by omega) ha hb; exact ⟨_,hc,fun {c f} g J F H ht x y=> h x y _ _ _ _ _ _ _ _ ht⟩) (fun i _ j _ x y u v hu hv {c f} g J F H ht p q=> (hu g J F H ht p q).trans (div_le_div_of_nonneg_right hv (by positivity)))
     obtain ⟨Z,hZ,HZ⟩:= pairBill (D:=D) (fun k m (p:Zinc G k)(q:Zinc G m)(C:ℝ)=> ∀ x∈Oasis ε s, ‖viewK p q x‖ ≤ C) (fun _=>inferInstance) (fun i _ j _ p q=>by
          obtain ⟨C,hC⟩:= (show IsCompact (Oasis ε s) from (isCompact_closedBall ..).inter_right (isOpen_ball.isClosed_compl)).bddAbove_image ((tepid he s G p q).norm); exact ⟨max C 0,le_max_right ..,fun x hx=>(hC (Set.mem_image_of_mem _ hx)).trans (le_max_left ..)⟩) (fun i _ j _ p q u v hu hv x h=> (hu x h).trans hv)
     let Cg (k m:ℕ) (p:Zinc G k)(q:Zinc G m)(C:ℝ):=∀ᶠ W:ℝ in atTop,∀ z:Cover,posT W n z∈Oasis ε s→∀ᶠ f:Side in atTop,∀ x y:Cover,∀ F:Bed,x-y=z → Grain a v b F f → W*‖(W^n)^(4+(stemP p).length+(stemP q).length) • pop1 (voteP f p x) (voteP f q y) (heartP F G f) () ()-viewK p q (posT W n z)‖ ≤ C
     obtain ⟨C,hc,h⟩:=pairBill (D:=D) Cg (fun _=>inferInstance) (fun k hk m hm p q=> by
          unfold Cg; simp_rw [vicar p q]; exact mainR (glimpse p) (glimpse q) p.1.2.1 q.1.2.1 p.2 q.2 _ _ (by omega) ha hv hb (rare p) (rare q) (gems p) (gems q) he s) (fun i _ j _ p q u v hu hv=>hu.mono fun w hw z hz=> (hw z hz).mono fun f hF x y A ht hX=>(hF x y A ht hX).trans hv)
     obtain ⟨T,hT,H'⟩:=firstP (D:=D) (fun i (p:Zinc G i)(s:ℝ)=> tollP p ≤ s) (fun _=>inferInstance) (fun i hi p=> ⟨_,toll_pos p,le_rfl⟩) (fun i _ p u v hv H=>hv.trans H)
     refine ⟨T+Y+M+P+Z+C+1,⟨by linarith,E,fun k hk p=>(H' k hk p).trans (by linarith),fun k hk m hm p q f F ht x y=>(H k hk m hm p q f F ht x y).trans (by linarith),fun k hk p {c f} g J F H h x z=> (HM k hk p g J F H h x z).trans (div_le_div_of_nonneg_right (by linarith : M ≤ _) (by positivity)),fun k hk m hm p q {c f} g J F H ht x y=> (HP k hk m hm p q g J F H ht x y).trans (div_le_div_of_nonneg_right (by linarith:P ≤ _) (by positivity)),fun k hk m hm p q x hx=> (HZ k hk m hm p q x hx).trans (by linarith),fun k hk m hm p q=>?_⟩⟩
     exact (show Cg k m p q C from h k hk m hm p q).mono fun w hw z hz=> (hw z hz).mono fun f h x y A ht hh=>(h x y A ht hh).trans (by linarith)
end YM.Bloom
#print axioms YM.Bloom.earns
