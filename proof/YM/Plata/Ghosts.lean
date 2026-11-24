import YM.Plata.Fan
import YM.Kly.Scad
import YM.Rill.Comes
/-!
outward polynomial. input spectral labels track ℂ at current actual cutoff (different per cut allowed). All extraction points inside contour.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Plata
open Function Filter Lattice Wilson Massive Massive.Lyre Massive.Romance Goblet
open QCD QCD.Lat QCD.Tide QCD.RP QCD.Plum -- hide Fields name
open Cylinder Patria Patria.Depth Patria.Hub Patria.Exposure Poised Poised.Plans Stamp
open YM.Fir Massive.Fir NoteF Metric Set Massive.Fir.TagF -- check used
open Tarn Choir
open Bridge (reflect Cluster carry) -- qualify reflecs...
open UV
open Needle
open scoped Topology BigOperators Classical ComplexOrder
-- all after cofinal regulator choices.
structure Bond where
       d:ℕ
       v:ℕ→Label d
       w:Label d
       s:ℕ → Cover
       x:E4
noncomputable abbrev Bearing (p:Bond)(i:ℕ):Stem:= ⟨p.d,p.v i,p.s i⟩
variable {Q:Choir}{C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}(h:Q.Harmony P φ)
set_option maxHeartbeats 310000
local notation "M" i:arg => C.S.spacing (C.N (φ i))
noncomputable abbrev vista (p:Bond):E4 ×Q.W:= (p.x,Q.focus none p.d p.w)
noncomputable abbrev wade (l:List Bond)(i:ℕ):= l.map fun p=> Bearing p i
noncomputable abbrev position (l:List Bond):Strip Q:= l.map vista
noncomputable abbrev Loc (C:Sequence)(φ:ℕ→ℕ)(s:ℕ→ Cover)(x:E4):Prop:= Tendsto (fun i=> digit (C.S.spacing (C.N (φ i))) (s i)) atTop (𝓝 x)
structure Inform (C:Sequence)(φ:ℕ→ℕ)(p:Bond): Prop where
       labelW: Tendsto p.v atTop (𝓝 p.w)
       source: Loc C φ p.s p.x
structure Worn (C:Sequence)(φ:ℕ→ℕ)(x:List Bond):Prop where
       extended (p:Bond) (hp:p∈x): Inform C φ p
variable {f:ℕ→ℕ}
noncomputable abbrev onward (f:ℕ→ℕ)(p:Bond):Bond:= {p with v:=p.v∘f,s:=p.s∘f}
lemma Worn.award (l: List Bond)(hy:Worn C φ l) (hf:Tendsto f atTop atTop): Worn C (φ∘f) (l.map (onward f)):=by
       constructor; intro p hp; obtain ⟨q,hq,rfl⟩:= List.mem_map.mp hp; constructor; · exact (hy.extended q hq).labelW.comp hf
       exact (hy.extended q hq).source.comp hf
lemma scent (l:List Bond)(f:ℕ→ℕ): position (Q:=Q) (l.map (onward f))= position l:=by simp only [position,List.map_map]; rfl
lemma waft (l:List Bond)(i:ℕ)(f:ℕ→ℕ): wade (l.map (onward f)) i=wade l (f i):=by simp only [wade,List.map_map]; rfl
open Needle
noncomputable abbrev impulse (P:Calibration C)(a:Axis)(b:ℕ→ Cover)(c:E4)(p:Bond): Bond:= ⟨p.d,fun i=> P.sym.adj p.d a (p.v i), P.sym.adj p.d a p.w,fun i=> (Signed.mirror a).act (p.s i)+b i,Ortho.move (Signed.reflect a) p.x+c⟩
lemma Inform.futureP (P:Calibration C) {a:Axis}{b:ℕ→ Cover}{c:E4}(p:Bond)(hy: Inform C φ p)(hc:Loc C φ b c): Inform C φ (impulse P a b c p):=by
       refine ⟨?_,?_⟩
       · have ht' : Continuous ⇑(P.sym.adj p.d a):=by
                let d:=p.d; let F:=P.sym.adj d a; let B:=Module.finBasis ℂ (Label d)
                have he(p:Label d): F p= ∑ j, star (B.coord j p) • F (B j):=by nth_rw 1 [← B.sum_repr p]; simp only [map_sum,map_smulₛₗ]; rfl
                rw [show ⇑(P.sym.adj p.d a) = _ from funext he]; exact continuous_finsetSum _ fun i _=> (continuous_star.comp ((B.coord i).continuous_of_finiteDimensional)).smul continuous_const
         exact (ht'.tendsto p.w).comp hy.labelW
       apply ((((Ortho.motion (Signed.reflect a)).continuous.tendsto _).comp hy.source).add hc).congr; intro i; change Ortho.motion (Signed.mirror a).ortho (digit (M i) _) + digit (M i) (b i)= digit (M i) (_+_); rw [digit_plus]; congr 1; unfold digit; rw[map_smul,Canvas.motion_site]
noncomputable abbrev inverted (P:Calibration C)(a:Axis)(b:ℕ→ Cover)(c:E4)(l:List Bond): List Bond:= l.reverse.map (impulse P a b c)
noncomputable abbrev Borne (P:Calibration C)(adj:Bool)(a:Axis)(y e:ℕ→ Cover)(p q:E4)(l:List Bond):List Bond:= if adj then inverted P a e q l else inverted P a e q (inverted P a y p l)
variable (l:List Bond)
lemma Worn.past (P:Calibration C)(h:Worn C φ l){a b c}(he:Loc C φ b c): Worn C φ (inverted P a b c l):=by
       constructor; intro p hp; obtain ⟨q,hq,rfl⟩:= List.mem_map.mp hp; exact Inform.futureP P _ (h.extended q (List.mem_reverse.mp hq)) he -- order
lemma Worn.pastP (P: Calibration C)(s:Bool)(a:Axis){b v:ℕ→ Cover}{p q:E4}(h:Worn C φ l)(hb:Loc C φ b p)(hv:Loc C φ v q): Worn C φ (Borne P s a b v p q l):=by cases s; exact Worn.past _ P (Worn.past _ P h hb) hv; exact Worn.past _ P h hv
lemma swirls (b:ℕ→ Cover)(a:Axis)(c:E4)(i:ℕ): wade (inverted P a b c l) i= sector P (wade l i) (b i) a:=by simp only [wade,inverted,List.map_map,sector,← List.map_reverse]; rfl
lemma curls (b v:ℕ→ Cover)(p q:E4)(a:Axis)(s:Bool)(i:ℕ):wade (Borne P s a b v p q l) i=passes P s a (b i) (v i) (wade l i):=by cases s<;>simp only[Borne,passes,Bool.false_eq_true,↓reduceIte,swirls]
variable (T:Pollens P Q)(A:EuPin→* (Q.W≃ₗ[ℂ] Q.W))(L: Ortho.Skew→Q.W→ₗ[ℂ] Q.W)
local notation "Fnz"=> equip T A L
lemma atFull (a:Axis)(c:E4)(p:ℕ→ Cover):position (Q:=Q) (inverted P a p c l)=carry (reflect (F:=Fnz) (position (Q:=Q) l) a) c:=by
       simp only[position,inverted,List.map_map, Bridge.reflectedPoint, carry, ← List.map_reverse]; congr 1; funext i; exact Prod.ext rfl (T.a a i.d none i.w).symm -- args
noncomputable abbrev Guilt (adj:Bool)(a:Axis)(p q:E4):= if adj then q else Ortho.move (Signed.reflect a) p+q
lemma omens (adj:Bool)(a:Axis)(p q:E4)(b v:ℕ→ Cover)(hr: Function.Involutive (T.adj a)): position (Q:=Q) (Borne P adj a b v p q l)= carry (F:=Fnz) (if adj then reflect (position (Q:=Q) l) a else position (Q:=Q) l) (Guilt adj a p q):=by
       cases adj; · simp only[Borne,Guilt, Bool.false_eq_true,↓reduceIte,atFull _ T A L]; rw [Bridge.refl_over, Bridge.paths]; congr 1; exact Bridge.reflect_twice a hr _ -- names
       exact atFull l T A L ..
open Strip
include h
lemma evaluationS (hz:Worn C φ l)(hx:distinct (position (Q:=Q) l)): Tendsto (fun i=> (C.A (φ i)).regulator.average (task P (φ i) (wade l i))) atTop (𝓝 (tone (position (Q:=Q) l))):=by
       let x:Points l.length:=points fun i=> (l.get i).x
       have ht:x∈conf _:=by
           have he:(l.map fun i=> i.x).Nodup:=by simpa only [position,List.map_map, comp_def] using (spots _).mp hx
           have ht := List.nodup_iff_injective_get.mp he
           intro i j hz; have ht':(Fin.cast (by simp) i: Fin (l.map fun i=> i.x).length)=Fin.cast (by simp) j:=ht (by change (l.get i).x=(l.get j).x at hz; simpa using hz); exact Fin.ext (by simpa using congr_arg Fin.val ht')
       let y(i:ℕ)(k:Fin l.length):= (l.get k).s i; let f(k:Fin l.length):=(l.get k).d; let W(i:ℕ)(k:Fin l.length): Label (f k):= (l.get k).v i
       have hu:Tendsto (fun i=>pollF C l.length (φ i) (y i)) atTop (𝓝 x):=by
           let Z:= PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin l.length=> E4); have he:Tendsto (fun i=>Z (pollF C _ (φ i) (y i))) atTop (𝓝 (Z x)):= tendsto_pi_nhds.mpr fun j=> (hz.extended _ (List.get_mem ..)).source
           have h:=(Z.symm.continuous.tendsto _).comp he; rw [Z.symm_apply_apply] at h; exact h
       let w(k:Fin l.length): Label (f k):= (l.get k).w; have hh:= h.exposed f (fun _=>none) w W (show Tendsto W atTop (𝓝 w) from tendsto_pi_nhds.mpr fun i=> (hz.extended (l.get i) (List.get_mem ..)).labelW) x ht; have he:Tendsto (fun i=>(i,y i)) atTop (Watch C φ x):=NoteF.ride (v:=fun i=>pollF C l.length (φ i)) _ _ tendsto_id hu
       rw [show tone (position (Q:=Q) l)= _ from introductions l]; refine (hh.comp he).congr (fun i=>?_); apply congr_arg ((C.A (φ i)).regulator.average); let F(j):=Stem.k P (φ i) (Bearing j i); change (List.ofFn (F ∘ l.get)).prod= (List.map _ _).prod; rw [←List.map_ofFn,List.ofFn_get]; simp only [wade,List.map_map]; rfl
where introductions (l:List Bond): tone (position (Q:=Q) l)= Q.total _ (points fun i=> (l.get i).x) fun i=> Q.focus none _ (l.get i).w := Strip.introduces ..
end YM.Plata
#print axioms YM.Plata.evaluationS
#print axioms YM.Plata.omens
