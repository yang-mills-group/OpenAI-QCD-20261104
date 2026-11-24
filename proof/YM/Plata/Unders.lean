import YM.Plata.Bamboo
import YM.Kly.Cape
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF
open YM.Plata Function Metric Set Finset
namespace Compass
open Choir Strip
variable {Q:Choir}{C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{S:Canopy.KForm Q}
noncomputable abbrev pebble(Q:Choir)(S:Canopy.KForm Q)(v:Strip Q): ℂ:= S v.length (Strip.locus v) (fun j=> (v.get j).2)
noncomputable abbrev pebG (Q:Choir)(S:Canopy.KForm Q)(v:List Bond): ℂ:= pebble Q S (Plata.position (Q:=Q) v)
lemma counter {n:ℕ} (v:Fin n→ Q.W)(x:Points n): pebble Q S (List.ofFn fun i:Fin n=> (x i,v i))= S n x v:=by
    let f(i:Fin n):= (x i,v i); generalize he:(List.ofFn (fun i:Fin n=> (x i,v i)))=l; have h:n=l.length:=by rw[←he,List.length_ofFn]
    let t:= locus (Q:=Q) l; let V:=(fun i:Fin l.length=>(l.get i).2); have hw (i:Fin n): l.get (Fin.cast h i)=f i:=by subst l; simp [f];
    have hc{n m:ℕ}(h:n=m)(x: Points n)(y:Points m)(p: Fin n→ Q.W)(q:Fin m→Q.W)(hp:∀ i,x i=y (Fin.cast h i))(hq:∀ i,p i=q (Fin.cast h i)): S m y q=S n x p:=by subst m; rw [PiLp.ext hp,funext hq]; simp
    exact hc h x t v V (fun i=> (congr_arg Prod.fst (hw i)).symm) (fun i=> (congr_arg Prod.snd (hw i)).symm)
open Massive.Bridge (Chamber Spread Cluster readAt)
open Massive.Bridge.Kly (bloom Steady dome)
open OS.Ground (Panes)
-- explicit universality/no Angle regulation in budgets
set_option quotPrecheck false
lemma zeal (T:Pollens P Q) (A:EuPin→* (Q.W≃ₗ[ℂ] Q.W)) (L: Ortho.Skew→ Q.W→ₗ[ℂ] Q.W)(V:Chamber (F:=equip T A L) Q.total timeAxis) (B: Spread V)(H:Steady V)(E:Massive.Fields.Euclidean (F:=equip T A L) Q.total)(hr:Involutive (T.adj timeAxis))(D: Panes B.algebra)(hd:D.Shines (dome V) B.algebra.subtype V.omega0)(t:B.algebra→⋆ₐ[ℂ]ℂ){β ε:ℝ}(hp:C.Path β ε)(hP:P.System)(hφ:Tendsto φ atTop atTop)(hQ:Q.Harmony P φ): Bankroll P φ Q (bloom B H t):=by
       refine ⟨hφ,⟨β,ε,hp⟩,hQ,Massive.Bridge.Kly.nilE B H E t,?_⟩; intro I hi σ ρ f z m g h hS hz hv hU hs; exact Plata.court (hQ.tuned hS) T A L hp hP (hφ.comp hS) z f h V B H E hr hz hv hs hU D hd t
variable {I:Type} [Fintype I]
variable (R:Bankroll P φ Q S)
include R
lemma bornK {D n:ℕ}(A:Compass C D)(X: Fin n→ Glyph D)(u:Fin n→ E4)(V:Legend)(hA: Known A)(hu:∀ i,X i∈ A.Ω)(hX:∀ i,(X i).material≠0)(hV:Pod P A φ V)(hn:n≤ A.K)(hs:u∈ flats (Fin n) (3*A.e) (A.v/4)):
       ‖S n (A.r • points u) (fun i=>choiceT V Q (X i).material)‖ ≤ A.dB^n:=by
       obtain ⟨β,e,ht⟩:=R.path; obtain ⟨g,Z,hf,hp,hZ⟩:= hV.proc; let f:= φ∘ g; let t:= A.r; have he:= R.flows.comp hf.tendsto_atTop
       choose y hy using fun i:Fin n=> choicesP P A Z f V ht he hp hZ hA _ (R.exposed.tuned hf.tendsto_atTop) X hu hX hn (u i)
       let Y(i:ℕ)(j):= y j i; let F(i):= A.qR (C.N i) ∘ Y i; have hv:Tendsto F atTop (𝓝 u):= tendsto_pi_nhds.mpr hy
       have hr:∀ᶠ i in atTop, F i ∈flats (Fin n) (2*A.e) (A.v/2):=by
            have ht : Tendsto (fun i=>‖F i-u‖) atTop (𝓝 0):=by simpa using (hv.sub_const u).norm
            filter_upwards [ht.eventually_lt_const (div_pos hA.live (by norm_num:(0:ℝ)<3)),ht.eventually_lt_const (div_pos hA.space (by norm_num:(0:ℝ)<10))] with i hi hp; exact puff _ _ u hs (F i) _ _ _ le_rfl (by linarith only[hi,hA.live]) (by linarith only [hp,hA.space])
       have hx:= noCol _ _ u hs (by linarith only [hA.live]); let w:=poisedP A Z f V X u Y
       have hm: Available P f (fun _:Unit=>w) (fun _=>1) (A.dB^n) (C.S.spacing A.pB) n:=by
            filter_upwards [he.eventually hr, he.eventually hZ] with i hi hz; unfold cash; simp only [Finset.univ_unique,Finset.sum_singleton,one_smul,w,fits]
            exact ballot _ _ _ _ _ hz hu hX hi hn -- args
       have he': Worn C f w:=fitP _ _ _ _ _ _ _ hp (hv.comp he)
       have h:= R.here (fun _:Unit=>w) (fun _=>1) n g (fun _=>uniqueP _ _ _ _ _ _ _ hx) hf.tendsto_atTop hm (fun _=>he') (pow_nonneg (zero_le_one.trans (gold0 ..)) n) (space0 C.S _)
       simp only [Finset.univ_unique,Finset.sum_singleton,one_mul] at h; change ‖pebG Q S w‖≤_ at h; unfold w pebG at h; rw [positionK,counter] at h; exact h
open Canopy
lemma given (E: Canopy P φ Q): Money E S:=by
       constructor; intro n x hx K hk hy; refine ⟨n,1,by norm_num,?_⟩
       filter_upwards [E.copperP x hx, E.care K hk hy 3 (1/4) (by norm_num) (by norm_num), E.many.eventually_ge_atTop n] with i h1 h2 h3 y h
       obtain ⟨F,hF⟩:=h1; let v(j:Fin n):= Vale.GlyphV (x j).2 _ (F j); have hp:= h2 h
       have hr:= bornK R (E.B i) v y.ofLp (E.V i) (E.trueK i) hF (fun k=>(hx k).1) (E.checkedW i).legit h3 (show y.ofLp∈ _ from ?_); swap
       · rw [show (E.B i).v/4=(1/4)* (E.B i).v from (by ring)]; exact hp
       rw [one_mul]; exact hr.trans (pow_le_pow_left₀ (zero_le_one.trans (Ibis.gold0 ..)) (E.bounded i) n)
end Compass
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Compass.zeal
#print axioms YM.Intag.Sprig.Compass.given
