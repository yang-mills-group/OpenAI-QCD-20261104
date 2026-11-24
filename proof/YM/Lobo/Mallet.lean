import YM.Lobo.Walt
set_option maxHeartbeats 760000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Finset
lemma orbitN(a b:Axis)(h:a≠b):∃ w:Bool,∃ i:Tri,(a,b)=hood w i∨(a,b)=(hood w i).swap:=by
     revert a b; change ∀ a b:Axis,a≠b→∃ _,∃ _,_∨_; unfold hood; classical
     intro a b h
     have he : ∀ a b:Axis,a≠b→∃ w:Bool,∃ i:Tri,(a,b)=(if w then (lieu i,timeAxis) else (lieu (edgeK i),lieu (backK i))) ∨ (b,a)=(if w then (lieu i,timeAxis) else (lieu (edgeK i),lieu (backK i))) := by decide
     obtain ⟨w,i,h|h⟩:= he a b h; · exact ⟨w,i,Or.inl h⟩
     exact ⟨w,i, Or.inr (congr_arg Prod.swap h)⟩
local notation "U"=> Label 8
private lemma zee {k:ℕ}(v:Label k)(h:v= -v):v=0:=by
       apply smul_right_injective (Label k) (two_ne_zero (α:=ℂ)); change (2:ℂ) • v=(2:ℂ) • (0:Label k); rw [smul_zero,two_smul]; nth_rw 1[h]; exact neg_add_cancel v
lemma shops (S: Submodule ℂ (Label 8))(hn:∀ w u i j,nodes w u i j∈S) : ∀ a b c d, GG a b c d∈S:=by
     have hx(a b:Axis)(v:Bool)(i:Tri): GG a b (hood v i).1 (hood v i).2 ∈ S:=by
          by_cases H:a=b; · subst b; rw [zee _ (turnL _ _ _ _)]; exact S.zero_mem
          obtain ⟨w,j,h|h⟩:= orbitN a b H; · rw [show a=_ from congr_arg Prod.fst h,show b=_ from congr_arg Prod.snd h]; exact hn ..
          rw [turnL, show a=_ from congr_arg Prod.fst h, show b=_ from congr_arg Prod.snd h]; exact ((show (- nodes w v j i: Label 8)∈ S from ((neg_one_smul ℂ (nodes w v j i)) ▸ Submodule.smul_mem S (-1:ℂ) (hn w v j i))))
     intro a b c d; by_cases H:c=d; · subst d; rw [zee _ (turnR a b c c)]; exact S.zero_mem
     obtain ⟨w,j,h|h⟩:= orbitN c d H; · rw [show c=_ from congr_arg Prod.fst h,show d=_ from congr_arg Prod.snd h]; exact hx ..
     rw [turnR, show c=_ from congr_arg Prod.fst h,show d=_ from congr_arg Prod.snd h]; exact (neg_one_smul ℂ (GG a b _ _)) ▸ S.smul_mem (-1:ℂ) (hx a b w j)
lemma harvest (S:Submodule ℂ U)(K:Spike→ₗ[ℂ] U)(h:∀ i:GammaRow,K (flat i)∈ S) (M:Spike): K M∈S:=by
     have hh : Submodule.span ℂ (Set.range flat) ≤ S.comap K:=Submodule.span_le.mpr fun x ⟨i,hi⟩=>hi ▸ h i; rw [spans] at hh; exact hh (Submodule.mem_top : M∈ (⊤:Submodule ℂ Spike))
variable {d:ℕ}{a:IceT}{F G:Tri→Tri→ Label d}(hF:BraceP a F)(hR:F=F)
noncomputable def opposite (F:Tri→Tri→ Label d): Tri→Tri→ Label d:= fun i j=> F j i
include hF
lemma transposeS : BraceP a (opposite F):=by
     refine ⟨fun K p i t h j k=>?_,fun i j=>hF.q j i⟩; rw [show opposite F j k= F k j from rfl,hF.cov K p i t h]; unfold wing; simp only [smul_sum]; rw[sum_comm]; apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; exact smul_comm _ _ (F y x)
lemma plusH (h:BraceP a G)(c:ℂ) : BraceP a (F+c • G):=by
       refine ⟨fun K p i t ht j k=>?_,fun i j=> (Qa d).add_mem (hF.q i j) ((Qa d).smul_mem c (h.q i j))⟩; simp only [Pi.add_apply,Pi.smul_apply,map_add,map_smul,hF.cov _ _ i t ht,h.cov _ _ i t ht]; unfold wing; simp only [smul_sum, Pi.add_apply, Pi.smul_apply,smul_add, sum_add_distrib]; congr 1; apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; rw [smul_comm c,smul_comm c]; -- fragile
omit hF
lemma monoB(F:Tri→Tri→ Label d)(hp:BraceP a F)(hx:∀ i j,F i j= -F j i) : Brook a (fun i=> F (edgeK i) (backK i)):=by
       refine ⟨fun K p i t ht j=>?_,fun i=> hp.q ..⟩; exact (hp.cov K p i t ht _ _).trans (heelL i j t F hx)
-- generate
include hF
lemma pairer (S:Submodule ℂ (Label d))(h:∀ (i:IceT)(u:Tri→Tri→Label d),BraceP i u→(∀ i j,u j i=u i j)→∀ j k,u j k∈S)(hk:∀ b:IceT,∀ u:Tri→Label d,Brook b u→∀ i,u i∈S)(p q:Tri): F p q∈ S:=by
      let H:= F+ (1:ℂ) • opposite F; let Z:= F+(-1:ℂ) • opposite F
      have he:BraceP a H:= plusH hF (transposeS hF) _; have ht:BraceP a Z:= plusH hF (transposeS hF) _; have hH(i j:Tri):H i j=F i j+F j i:=by unfold H; rw [one_smul]; rfl
      have hZ(i j:Tri):Z i j= F i j - F j i:=by change F i j + (-1:ℂ) • F j i= _; rw [show (-1:ℂ) • F j i = _ from neg_one_smul ℂ (F j i)]; exact (sub_eq_add_neg (F i j) (F j i)).symm
      have hz(i j:Tri): Z i j= -(Z j i):=by rw [hZ,hZ]; exact (neg_sub (F j i) (F i j)).symm -- orientation
      have hy(k):Z k (edgeK k)∈ S:= by have h:= hk a _ (monoB Z ht hz) (backK k); exact (by simpa only[(tracesI k).2.2.1,(tracesI k).2.2.2] using h)
      have h': Z p q∈S:=by
           obtain rfl|h|h:= stateU p q; · rw [zee _ (hz q q)]; exact S.zero_mem
           · rw[h]; exact hy _
           rw[h,hz]; have hv:=hy (backK p); rw [(tracesI p).2.2.1] at hv; exact (neg_one_smul ℂ (Z (backK p) p)) ▸ S.smul_mem (-1:ℂ) hv
      apply (S.smul_mem_iff (two_ne_zero (α:=ℂ))).mp
      have hw : (2:ℂ) • F p q= H p q+Z p q:=by rw[hH,hZ,two_smul]; abel
      rw[hw]; exact S.add_mem (h a H he (fun i j=>by rw [hH,hH,add_comm]) _ _) h'
omit hF
lemma earnest (S:Submodule ℂ U)(s:RawSym)(hs:∀ (b:IceT)(u:U), Lone b u → u∈ S)(he:∀ b:IceT,∀ u:Tri→Label 8,Brook b u→∀ i,u i∈ S)(hk:∀ (i:IceT)(u:Tri→Tri→U), BraceP i u → (∀ i j,u j i=u i j)→∀ i j,u i j∈ S) : Qa 8 ≤ S:=by
     refine fun x hx=> grove x hx S s (hs none _ (oneH s)) (shops S (fun w u i j=>pairer (crestT w u) S hk he i j)) (fun f M=>?_)
     have h0:gulf f M∈S:= harvest S _ (fun | (none,u,v)=> hs _ _ (twirp f u v) | (some j,u,v)=> he _ _ (twirl f u v) j) M
     have h(a:Axis)(w:Bool): swamp f a w M ∈ S:=by
               rcases Fin.eq_castSucc_or_eq_last a with ⟨i,hi⟩|hl -- name
               · rw [hi]; exact harvest S (swamp f (lieu i) w) (fun | (none,u,v)=> he _ _ (spanT f w u v) i| (some j,u,v)=> pairer (spearT f w u v) S hk he i j) M
               rw [hl]; exact harvest S (swamp f timeAxis w) (fun | (none,u,v)=>hs _ _ (spinT f w u v)| (some j,u,v)=>he _ _ (spunS f w u v) j) M
     exact ⟨h0, fun i=>⟨h i true,h i false⟩⟩
end YM.Lobo
#print axioms YM.Lobo.earnest
