import YM.Tarn.Waltz
/-! Literal ensemble moments. List coherence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open Function QCD QCD.Lat Wilson Patria Patria.Depth Patria.Hub Lattice Cylinder Dispersed Fir YM.Fir UV Filter Set TensorProduct
open Poised Poised.Plans Poised.Plans.Stamp QCD.Grass Needle
open scoped Topology BigOperators Classical
variable {C:Sequence} {P:Calibration C} {β e:ℝ}(hp:C.Path β e) {n:ℕ} {Q: Choir} {φ:ℕ→ℕ}(h:Q.Harmony P φ)(hφ:Tendsto φ atTop atTop)(hQ:P.System)
abbrev Strip (Q:Choir):= List (E4×Q.W)
abbrev lap (Q: Choir)(u: Averaging)(x:TagF): Q.W:= Q.focus u x.1 x.2
namespace Strip
abbrev locus (v: Strip Q): Points v.length:=points fun i=> (v.get i).1
noncomputable abbrev tone (v:Strip Q):ℂ:= Q.total _ (locus v) (fun i=> (v.get i).2)
abbrev distinct (v:Strip Q):= locus v∈conf v.length
lemma spots (v:Strip Q): Strip.distinct v ↔ (v.map Prod.fst).Nodup := by
    let f:= fun i=> (v.get i).1; have he : v.map Prod.fst=List.ofFn f:=by rw [show f=Prod.fst ∘ v.get from rfl,←List.map_ofFn,List.ofFn_get]
    rw [he,List.nodup_ofFn]; rfl
lemma fresh (l:Strip Q) {x: E4×Q.W}(hx:Strip.distinct (x::l)) : Strip.distinct l:= (spots _).mpr (List.Nodup.of_cons ((spots _).mp hx)) -- names
-- generic sequence programs. list of specimens.Spec. Hold rep. point families pilots
structure Petal (P:Calibration C) where
     fieldT:TagF
     r:ℕ→ Cover -- along i AFTER subsection.
     x:E4
abbrev petals (Q: Choir)(u:Averaging)(l: List (Petal P)):Strip Q:= l.map fun j=> (j.x,lap Q u j.fieldT)
noncomputable abbrev signalW (u:Averaging)(j:Petal P)(φ:ℕ→ℕ)(i:ℕ):= P.physical u (φ i) j.fieldT.2 (j.r i)
noncomputable abbrev chalk (Q: Choir) {E:Type*} (x:E→ E4) (s:E→Q.W)(l:List E): ℂ:=tone (l.map fun i=>(x i,s i) : Strip Q)
lemma introduces {E:Type*} (x:E→ E4)(s:E→Q.W)(l:List E) : chalk Q x s l= Q.total l.length (points fun i=> x (l.get i)) (fun i=>s (l.get i)):=by -- Q shadow
     unfold chalk tone; generalize hl:(l.map fun i=> (x i,s i):Strip Q)=v; have hv: v.length=l.length:=by rw [←hl,List.length_map]
     let y:= points fun i=> x (l.get i); let w:=(fun i=>s (l.get i)); let u:=locus v; let t:=fun i:Fin v.length=>(v.get i).2; have hF(i): v.get i= (x (l.get (Fin.cast hv i)),s (l.get (Fin.cast hv i))):=by subst v; simp
     have he: ∀ (n m:ℕ)(h:n=m)(x:Points n)(y: Points m)(p:Fin n→Q.W)(q:Fin m→Q.W), (∀ i,x i=y (Fin.cast h i))→(∀ i,p i=q (Fin.cast h i)) → Q.total n x p=Q.total m y q:= by intro n m h; subst m; intro x y p q h H; rw [show x=y from PiLp.ext h, show p=q from funext H]
     exact he _ _ hv u y t w (fun i=>congr_arg Prod.fst (hF i)) (fun i=> congr_arg Prod.snd (hF i))
include h
lemma reaches (l:List (Petal P))(V:Averaging)(hx: Strip.distinct (petals Q V l))(hz:∀ i∈l,Tendsto (fun k=> digit (C.S.spacing (C.N (φ k))) (i.r k)) atTop (𝓝 i.x)): Tendsto (fun i=> ((C.A (φ i)).regulator).average (l.map fun j=> signalW V j φ i).prod) atTop (𝓝 (Strip.tone (petals Q V l))):=by
      let x:Points l.length:=points fun i=> (l.get i).x
      have ht:x∈conf _:=by
           have he:(l.map fun i=> i.x).Nodup:=by simpa only [petals,List.map_map, comp_def] using (spots _).mp hx
           have ht := List.nodup_iff_injective_get.mp he
           intro i j hz; have ht':(Fin.cast (by simp) i: Fin (l.map fun i=> i.x).length)=Fin.cast (by simp) j:=ht (by change (l.get i).x=(l.get j).x at hz; simpa using hz); exact Fin.ext (by simpa using congr_arg Fin.val ht')
      let y(i:ℕ)(k:Fin l.length):= (l.get k).r i; let f(i:Fin l.length):=(l.get i).fieldT
      have hu:Tendsto (fun i=>pollF C l.length (φ i) (y i)) atTop (𝓝 x):=by
           let Z:= PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin l.length=> E4); have he:Tendsto (fun i=>Z (pollF C _ (φ i) (y i))) atTop (𝓝 (Z x)):= tendsto_pi_nhds.mpr fun j=> hz _ (List.get_mem ..)
           have h:=(Z.symm.continuous.tendsto _).comp he; rw [Z.symm_apply_apply] at h; exact h
      have hh:= h.picks (fun i=> (f i).1) (fun _=>V) (fun i=>(f i).2) x ht hu; rw [show tone (petals Q V l)= _ from (introduces (x:=fun i:Petal P=> i.x) (s:=fun i=>lap Q V i.fieldT) ..)]; refine hh.congr (fun i=> ?_); apply congr_arg ((C.A (φ i)).regulator.average); let F(j):=signalW V (P:=P) j φ i; change (List.ofFn (F ∘ l.get)).prod= (l.map F).prod; rw[←List.map_ofFn,List.ofFn_get]
end Strip
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.Strip.reaches
