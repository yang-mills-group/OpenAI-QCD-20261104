import YM.Gust.Wig
set_option maxHeartbeats 640000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis MeasureTheory Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C: Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T){m n k:ℕ}
open Tarn.ChargeQ
variable (A:Axis×Axis→K.W) (hA:Persona T A)
local notation "L"=>fun a b=>A (a,b)
variable (J:Axle K (fun a b=>A (a,b))) (U:Vane J)
variable (B:K.W) {x:Points (m+1)}(hx:x∈conf _)(p:Fin m→K.W) {χ:E4→ℝ}(hw:Table.Window x χ)
include hf hA
lemma art_pair (z:E4)(hz:Points.cons z x∈conf _)(a b:Axis) : K.total _ (Points.cons z x) (Fin.cons (A (a,b)) (T.parity ∘ Fin.cons B p)) = phot (L) (Fin.cons B p) x a b z:=by
       have h:= hf.parity _ _ hz (Fin.cons (A (a,b)) (Fin.cons B p)); rw [Fin.comp_cons,hA.tense.parity] at h; exact h
variable (g:Ortho.Skew)
include hx hw
lemma timesG: fluxG (L) χ (fun y=> M4.move g.val (y-x 0)) x (T.parity ∘ Fin.cons B p)=fluxG (L) χ (fun y=> M4.move g.val (y-x 0)) x (Fin.cons B p):=by
       unfold fluxG; congr 1; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; congr 1; funext y; by_cases h:D (basis a) χ y=0; · simp[termG,h]
       unfold termG; rw [art_pair hf A hA B p y (Work.A01.separated_of_D hx hw h)] -- after `_` args
lemma runsG(a:Axis):gradG (L) χ a x (T.parity ∘p) (T.parity B)=gradG (L) χ a x p B:=by
       unfold gradG; congr 1; apply Finset.sum_congr rfl; intro i _; congr 1; funext y; by_cases h:D (basis i) χ y=0; · simp [h];
       rw [← Fin.comp_cons]; exact congr_arg _ (art_pair hf A hA B p y (Work.A01.separated_of_D hx hw h) i a)
omit hx hw
include hK
lemma Axle.colors :J.jet g (T.parity B)= T.parity (J.jet g B):=by
       apply detected hf; intro n p x hx; let v:=T.parity ∘p; have hv:T.parity ∘v=p:=funext fun i=>T.even hK _; obtain ⟨χ,hχ⟩:=Work.A01.exists_window x hx
       have h:=timesG hf A hA B hx v hχ g; rw [Fin.comp_cons,hv] at h; refine Eq.trans (J.relation g _ n x χ hx hχ _).symm (Eq.trans h ?_); refine Eq.trans (J.relation g B n x χ hx hχ v) ?_; rw [heads,heads,← hf.parity n.succ x hx (Fin.cons _ v),Fin.comp_cons,hv]
lemma Vane.colors (a:Axis): U.edge a (T.parity B)= T.parity (U.edge a B):=by
       apply detected hf; intro n p x hx; let v:= T.parity ∘p; have hv:T.parity ∘v=p:=funext fun i=>T.even hK _; obtain ⟨χ,hχ⟩:= Work.A01.exists_window x hx; rw [←U.snaps n x p χ hx hχ a (T.parity B)]; nth_rw 1 [←hv]; rw [runsG hf A hA B hx v hχ a,U.snaps _ _ _ _ hx hχ a B, heads,heads,← hf.parity (n+1) x hx (Fin.cons _ v),Fin.comp_cons,hv] -- hx index
noncomputable def swirl(K:Choir)(A:Axis×Axis→K.W)(J:Axle K (fun a b=>A (a,b)))(U:Vane J)(g: Ortho.Skew)(x:E4)(B:K.W):= J.jet g B+∑ b:Axis, (M4.move g.val x b:ℂ) • U.edge b B
lemma coat(b:Bool)(h:B∈ Col T b)(x:E4): swirl K A J U g x B∈ Col T b:=by
       have ht:= (hue ..).1 h; unfold swirl; apply Submodule.add_mem; · rw [hue, ←Axle.colors hK hf A hA,ht,map_smul]
       apply Submodule.sum_mem; intro i _; apply Submodule.smul_mem; rw[hue,←Vane.colors hK hf A hA,ht,map_smul]
-- signed swap of original list & shifted index with one-way compensation only. Universal existence c works for deck q/p and stress.L proof simultaneously for all y.
variable {I :Type*}
abbrev TwistPlace (f:I→E4)(p:I→K.W)(u:List I): Strip K:= u.map fun i=>(f i,p i)
variable (α β:List I)
lemma orderPres (s:I→Bool) (h:α.Perm β) (γ:List I):∃ c:ℂ,c≠0 ∧∀ f:I→E4,∀ p:I→K.W,(∀ i,p i∈ Col T (s i)) →∀ l:Strip K, Strip.distinct (l++ TwistPlace f p (γ++α)) → tone (l++TwistPlace f p (γ++β))=c*tone (l++TwistPlace f p (γ++α)):=by
       induction h generalizing γ with
       | nil=> exact ⟨1,one_ne_zero,fun _ _ _ _ _=> (one_mul _).symm⟩
       | @cons i x y h ih=> obtain ⟨c,h,hp⟩:= ih (γ++[i]); exact ⟨c,h,fun f p h l hx=>by simpa [List.append_assoc] using hp f p h l (by simpa [List.append_assoc] using hx)⟩
       | @swap i j L' =>
             let c:ℂ:= if s i && s j then -1 else 1; refine ⟨c,(by unfold c; split <;> norm_num),fun f p h l hx=>?_⟩; let g(i):=(f i,p i); let q:= l++ γ.map g; let K':= L'.map g
             have hh : Strip.distinct (q++g i::g j::K'):=by
                    have hu : List.Perm (l++TwistPlace f p (γ++j::i::L')) (l++TwistPlace f p (γ++i::j::L')):= ((List.Perm.swap i j L'|>.append_left γ).map g).append_left l
                    have h:Strip.distinct (l++TwistPlace f p (γ++i::j::L')):=(Strip.spots _).2 ((hu.map Prod.fst).nodup ((Strip.spots _).1 hx))
                    simpa only [q,K',TwistPlace,List.map_append,List.map_cons,List.append_assoc] using h
             have hz(x): markedW T (s x) (p x):=by unfold markedW; rw[(hue ..).1 (h x)]; cases h':s x<;>simp[tauMod]
             simpa only [q,K',TwistPlace,List.map_append,List.map_cons,List.append_assoc] using hf.flips q K' (g i) (g j) _ _ hh (hz i) (hz j)
       | @trans x y z h v ht hw=>
             obtain ⟨c,hc,hQ⟩:= ht γ; obtain ⟨d,hd,H⟩:= hw γ; refine ⟨d*c,mul_ne_zero hd hc,fun f p hP l hx=>?_⟩; have hh: Strip.distinct (l++TwistPlace f p (γ++y)):=by apply (spots _).2; exact (((((h.append_left γ).map (fun i => (f i,p i))).append_left l).map Prod.fst).nodup ((spots _).mp hx)); -- fix
             rw [H f p hP l hh,hQ f p hP l hx,mul_assoc]
end YM.Massive.Gust
#print axioms YM.Massive.Gust.orderPres
#print axioms YM.Massive.Gust.coat

