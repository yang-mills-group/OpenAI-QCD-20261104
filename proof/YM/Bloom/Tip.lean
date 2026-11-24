import YM.Bloom.Task
/-! # EyesS at budget ALL flavor horizons allowed. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bloom
open Function Lattice Laurent Bloch Metric RG Filter Arise Arise.Range Massive UV UV.Free
open Finset YM.Bank Precision Matrix YM.Bloom
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Classical
open QCD QCD.Lat QCD.Free QCD.Flume QCD.Bank Next.Free YM.Bloom.TreeP
open QCD.Creek QCD.Anomaly QCD.Cove QCD.Grass
open Buzz YM.Bank.Jule YM.Bank.Pic YM.Bloom.Jar
variable {c f:Side}{N r k m n l b ℓ j s D d L:ℕ}{A J Y:Type}[Fintype A][Fintype J][Fintype Y]
abbrev Sings (d:ℕ):= Pairs (SpinMode d)
abbrev chief (p:Sings d): Bool:= Sum.elim (fun _=>false) (fun _=>true) p
abbrev coreW (p:Sings d): SpinMode d := Sum.elim id id p
abbrev order_p (p: Sings d): ℕ:= (steps (coreW p).1.1).length
lemma measures (p:Sings d):order_p p≤ d := (spine_cost _).trans_le (coreW p).1.1.property
noncomputable def footprintP (p:Sings d):Parc:= came (rider (coreW p).1.1)
lemma spanned_p (p:Sings d): footprintP p∈ Arise.tails (order_p p) (d+1):= recovered _ _ _ _ (measures p) (rideOn _)
noncomputable def tokenS (f:Side)(p:Sings d)(x:Cover): Matrix Unit (Keys f 6) ℂ:= Buzz.paint f x (coreW p).1.2 (coreW p).2 (footprintP p) (chief p)
noncomputable def pin (p:Sings d)(q:Sings k)(x y:E4):ℂ:= if chief p=false ∧ chief q=true then leg (coreW p) (coreW q) x y else 0
lemma pin_ch (p:Sings d)(q:Sings k)(x y:E4): pin p q x y=pin p q (x-y) 0:=by unfold pin leg; rw [sub_zero]
lemma heated (p:Sings d)(q:Sings k)(x:E4)(hx:x≠0): ContinuousAt (fun x=>pin p q x 0) x:=by
    unfold pin; by_cases he:chief p=false ∧ chief q=true; swap
    · simp only [if_neg he]; exact continuousAt_const
    simp only [if_pos he]; let A:=coreW p; let B:=coreW q; let F:E4→ℂ:= if A.2=B.2 then stove (YM.Bank.Ivo.s_k A.1.2 B.1.2) (steps A.1.1) (steps B.1.1) else 0
    have h:(fun v=>leg A B v 0)=ᶠ[𝓝 x] F :=by
         filter_upwards [Maxwell.open_away.mem_nhds hx] with x hx; rw [tours x 0 A B hx]; unfold F; by_cases ht:A.2=B.2<;> simp only [ht,↓reduceIte,sub_zero,Pi.zero_apply,not_false_eq_true]
    apply ContinuousAt.congr (f:=F) _ h.symm; unfold F; split; · exact swipe_p _ _ _ _ x hx
    exact continuousAt_const
noncomputable def sur (p:Sings d):= audit (flet (footprintP p)) 6 * pattern (footprintP p)
lemma solemn (p:Sings d): 0≤ sur p:=by unfold sur; exact mul_nonneg (by unfold audit; positivity) (valor_g _)
lemma startsU (p:Sings d)(x:Cover): cusp (tokenS c p x) ()≤ sur p:=money_p x _ _ _ _
noncomputable abbrev craw {F: Matrix (Keys f 6) (Keys f 6) ℂ}(p q:Matrix Unit (Keys f 6) ℂ):= p*F*q.transpose
noncomputable def lowT {c f:Side}(E: Train j)(P: Matrix (Keys f 6) (Keys c 6) ℂ) := P*Buzz.start c E 6*P.transpose
structure Spar (D L n j:ℕ)(ε s C:ℝ): Prop where
    pay: 0 < C
    span k(h:k ≤ D)(p:Sings k) : flet (footprintP p)≤ L
    price k(h:k ≤ D)(p:Sings k): sur p ≤ C
    youth k(h:k ≤ D)m(ht:m ≤ D)(p:Sings k)(q:Sings m)(f:Side)(F:Train j)(x y:Cover) : ‖(tokenS f p x*start f F 6*(tokenS f q y).transpose) () ()‖≤ C
    ask k(h:k ≤ D)(p:Sings k){c f:Side}(g:Ratio c f)(F H:Train j){U X Q}(ht:Giant j g F H U X Q)(x:Cover)(z:Keys c 6): ‖(tokenS f p x*Buzz.wheel U X 6) () z‖ ≤ C*gear g.count (order_p p)
    pearly k(h:k ≤ D)m(ht:m ≤ D)(p:Sings k)(q:Sings m){c f:Side}(g: Ratio c f)(F H:Train j){U X Q}(he:Giant j g F H U X Q)(x y:Cover): ‖(tokenS f p x*lowT H (Buzz.wheel U X 6)*(tokenS f q y).transpose) () ()‖≤ C*(gear g.count (order_p p)*gear g.count (order_p q))
    sense k(h:k ≤ D)m(ht:m ≤ D)(p:Sings k)(q:Sings m)(x:E4)(hx:x∈ Oasis ε s):‖pin p q x 0‖≤ C
    compare k(h:k ≤ D)m(ht:m ≤ D)(p:Sings k)(q:Sings m):∀ᶠ W:ℝ in atTop,∀ z:Cover,posT W n z∈Oasis ε s →∀ᶠ f:Side in atTop,∀ x y:Cover,x-y=z → ∀ F:Train j, W*‖ (W^n)^(3+order_p p+order_p q) • (tokenS f p x*start f F 6*(tokenS f q y).transpose) () () - pin p q (posT W n x) (posT W n y)‖ ≤ C
lemma extendsS (D:ℕ): ∃ L:ℕ,∀ k ≤ D,∀ p:Sings k, flet (footprintP p)≤ L:=by
    let W(k:ℕ):ℕ:=univ.sup fun p:Sings k=> flet (footprintP p); refine ⟨(Finset.range (D+1)).sup W,?_⟩; intro k hk p; have h:flet (footprintP p)≤ W k:=Finset.le_sup (f:=fun p:Sings k=> flet (footprintP p)) (mem_univ p); exact h.trans (le_sup (f:=W) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
lemma spiny (ε b:ℝ) (he:0<ε)(hj:D+3≤ j)(hn:10+2*D ≤ n)(E:∀ k ≤ D,∀ p:Sings k, flet (footprintP p)≤ L):∃ C:ℝ,Spar D L n j ε b C:=by
     let hY(k m:ℕ)(p:Sings k)(q:Sings m)(C:ℝ):= ∀ (f:Side)(F:Train j)(x y:Cover), ‖(tokenS f p x*start f F 6*(tokenS f q y).transpose) () ()‖≤ C
     obtain ⟨Y,hy,H⟩:=pairBill (D:=D) hY (fun i=>inferInstance) (fun k hk m hm p q=>by obtain ⟨C,hc,h⟩:=buy_unit (N:=6) _ _ (spanned_p p) (spanned_p q) (show k+1+2≤j by omega) (by omega); exact ⟨_,hc,fun f F x y=> h f _ _ _ _ _ _ _ _ F⟩) (fun i _ j _ x y u v hu hv f F x y=> (hu f F x y).trans hv)
     let P(k:ℕ)(p:Sings k)(C:ℝ):=∀ {c f:Side}(g: Ratio c f)(F H:Train j){U X Q}(ht:Giant j g F H U X Q)(x:Cover)(z:Keys c 6), ‖(tokenS f p x*Buzz.wheel U X 6) () z‖ ≤ C*gear g.count (order_p p)
     obtain ⟨U,hU,HU⟩:=firstP (D:=D) P (fun i=>inferInstance) (fun i hi p=>by obtain ⟨C,hc,h⟩:= paint_budget (N:=6) _ (spanned_p p) (show i+1+2≤j by omega); exact ⟨C,hc,fun {c f} g F H {U X Q} h' x z=> h _ _ _ _ _ _ _ h' z⟩) (fun i _ p u v h hv {c f} g F H {U X Q} ht x z=> (h g F H ht x z).trans (mul_le_mul_of_nonneg_right hv (gear_pos ..).le))
     let V(k m:ℕ)(p:Sings k)(q:Sings m)(C:ℝ):=∀ {c f:Side}(g: Ratio c f)(F H:Train j){U X Q}(ht:Giant j g F H U X Q)(x y:Cover), ‖(tokenS f p x* lowT H (Buzz.wheel U X 6) * (tokenS f q y).transpose) () ()‖ ≤ C*(gear g.count (order_p p)*gear g.count (order_p q))
     obtain ⟨J,hJ,HJ⟩:= pairBill (D:=D) V (fun i=>inferInstance) (fun i hi m hm p q=> by obtain ⟨C,hc,h⟩:=sailS (N:=6) _ _ (spanned_p p) (spanned_p q) (show i+1+2 ≤ j by omega) (by omega); exact ⟨C,hc,fun {c f} g F H {U X Q} ht x y=>h _ _ _ _ _ _ _ _ _ _ _ ht⟩) (fun i _ j _ p q u v hu hv {c f} g F H {U X Q} ht x y=> (hu g F H ht x y).trans (mul_le_mul_of_nonneg_right hv (mul_nonneg (gear_pos ..).le (gear_pos ..).le)))
     obtain ⟨Z,hZ,HZ⟩:=pairBill (D:=D) (fun k m (p:Sings k)(q:Sings m) C=> ∀ x∈Oasis ε b, ‖pin p q x 0‖ ≤ C) (fun i=>inferInstance) (fun i _ m _ p q=> by
          obtain ⟨C,hc⟩:=(show IsCompact (Oasis ε b) from (isCompact_closedBall ..).inter_right isOpen_ball.isClosed_compl).bddAbove_image (show ContinuousOn (fun x=> ‖pin p q x 0‖) (Oasis ε b) from fun x hx=> (heated p q x (door hx he)).norm.continuousWithinAt); exact ⟨max C 0,le_max_right ..,fun i hi=> (hc (Set.mem_image_of_mem _ hi)).trans (le_max_left ..)⟩) (fun i _ j _ p q u v hu hv x hx=>(hu x hx).trans hv)
     let T (k m:ℕ)(p:Sings k)(q:Sings m)(C:ℝ):=∀ᶠ W:ℝ in atTop,∀ z:Cover,posT W n z∈Oasis ε b→∀ᶠ f:Side in atTop,∀ x y:Cover,x-y=z →∀ F:Train j,W*‖ (W^n)^(3+order_p p+order_p q) • (tokenS f p x*start f F 6*(tokenS f q y).transpose) () ()-pin p q (posT W n x) (posT W n y)‖≤ C
     obtain ⟨B,hB,HB⟩:=pairBill (D:=D) T (fun i=>inferInstance) (fun i hi m hm p q=>spirals (footprintP p) (footprintP q) _ _ (by omega) (by omega) he b (chief p) (chief q) (rideOn _) (rideOn _)) (fun i _ j _ p q u v hu hv=> hu.mono fun w hw z hz=> (hw z hz).mono fun f hf x y ht F=> (hf x y ht F).trans hv)
     obtain ⟨G,hG,H'⟩:=firstP (D:=D) (fun k (p:Sings k) C=> sur p≤ C) (fun i=>inferInstance) (fun i _ p=>⟨_,solemn p,le_rfl⟩) (fun i _ p u v h hv=> h.trans hv)
     let C:= G+B+Z+J+U+Y+1
     have hu:U ≤ C:=by unfold C; linarith
     have hv:J ≤ C:=by unfold C; linarith
     refine ⟨C,?_⟩; unfold C; exact ⟨by linarith,E,fun k hk p=> (H' k hk p).trans (by linarith),fun k hk m hm p q f F x y=> (H k hk m hm p q f F x y).trans (by linarith),fun k hk p {c f} g F H {U X Q} ht x z=> (HU k hk p g F H ht x z).trans (mul_le_mul_of_nonneg_right hu (gear_pos ..).le),fun k hk m hm p q {c f} g F H {U X Q} ht x y=> (HJ k hk m hm p q g F H ht x y).trans (mul_le_mul_of_nonneg_right hv (mul_nonneg (gear_pos ..).le (gear_pos ..).le)),fun k hk m hm p q x hx=>(HZ k hk m hm p q x hx).trans (by linarith),fun k hk m hm p q=> (show T k m p q B from HB k hk m hm p q).mono (fun w hw z hz=>(hw z hz).mono fun f h x y he F=>(h x y he F).trans (by linarith))⟩
end YM.QCD.Bloom
#print axioms YM.QCD.Bloom.spiny
