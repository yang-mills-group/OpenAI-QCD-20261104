import YM.MassiveBridge.Phosphors

/-!
# OS Chambers are separable

using the actual finite-level and exhaust properties, and scalar topologies
already in the statement, not any joint distribution or Lorentz input. Needed
here instead of assuming closure onto the W subspace. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Function Set Filter MeasureTheory
open Boundary hiding Fields Surface Soil Scroll Waves Letter Sentence Action Outfield
open scoped Topology NNReal BigOperators InnerProductSpace ComplexOrder Matrix.Norms.Frobenius
variable {F:Fields} {S:F.Kernel} {Q:Sequence} {P:Calibration Q} {a:Axis} {C:Chamber S a}
namespace Chamber
open Fields (pointMoment)
open TopologicalSpace
variable {d n:ℕ} (C:Chamber S a)

abbrev CapIn (F:Fields) (n d:ℕ):= Points n × (Fin n → F.level d)
abbrev parcels (x:CapIn F n d): Cluster F:= realize ((F.level d).subtype ∘ x.2) x.1
abbrev CapZone (n d:ℕ)(a:Axis)(F:Fields):= {x:CapIn F n d// Positive (parcels x) a}

def sample (n d:ℕ) (x:CapZone n d a F): C.H:= C.GNS.plant ⟨parcels x.val,x.property⟩

-- evaluate scalar kernel both sides varying together on an arity/degree piece
lemma sample_both [FiniteDimensional ℂ (F.level d)] (p:Fields.Euclidean S): Continuous fun v : CapZone n d a F × CapZone n d a F=> inner ℂ (C.sample n d v.1) (C.sample n d v.2):=by
   classical
   let U:= CapZone n d a F × CapZone n d a F
   let z(t:U):Points (n+n):= points (Fin.append (fun i: Fin n=> Ortho.move (Signed.reflect a) (t.1.val.1 i.rev)) t.2.val.1.ofLp)
   let h(t:U): Fin (n+n)→F.W:= Fin.append (fun i:Fin n=> F.adj a (t.1.val.2 i.rev).val) (fun i:Fin n=> (t.2.val.2 i).val)
   have he (t:U): reflect (parcels t.1.val) a ++ parcels t.2.val= realize (h t) (z t):=by
     unfold parcels realize
     let l : Fin n→ Plant F := fun i=> (Ortho.move (Signed.reflect a) (t.1.val.1 i.rev), F.adj a (t.1.val.2 i.rev).val)
     let r : Fin n → Plant F:=fun i=> (t.2.val.1 i,(t.2.val.2 i).val)
     have hz: (fun i=> (z t i,h t i))= Fin.append l r:=funext fun i=> Fin.addCases (fun k=> by simp only [z,h,points_apply,Fin.append_left]; rfl) (fun k=> by simp only [z,h,points_apply,Fin.append_right];rfl) i
     rw [hz,List.ofFn_fin_append]; congr 1
     rw [reflectedPoint,List.map_reverse,List.map_ofFn]
     have e (g:Fin n→Plant F): (List.ofFn g).reverse= List.ofFn (fun i=>g i.rev) := by
       refine List.ext_get (by simp) (fun i H X=>?_)
       rw [List.get_ofFn, List.get_eq_getElem, List.getElem_reverse,List.getElem_ofFn]
       have he:i<n:=by simpa using X
       apply congrArg g
       apply Fin.ext
       simp [Fin.val_rev];omega
     exact e _
   unfold sample; simp_rw [C.GNS.measure]
   change Continuous fun t:U=> pointMoment S (reflect (parcels t.1.val) a ++ parcels t.2.val)
   have hz (t:U): z t∈ conf _:= by
     have ht:=twoSides t.1.property t.2.property
     rw [he] at ht; exact (realized ..).1 ht
   have hZ:Continuous z := by
     unfold z points
     apply (PiLp.homeomorph 2 _).symm.continuous.comp
       (f:=fun t:U=> (z t).ofLp)
     refine continuous_pi fun i=>?_
     refine Fin.addCases (fun i=>?_) (fun i=>?_) i
     · simp only [z,points_apply,Fin.append_left]; exact (Ortho.motion _).continuous.comp (show Continuous (fun t:U=>t.1.val.1 i.rev) by unfold U CapZone CapIn;fun_prop)
     simp only [z,points_apply,Fin.append_right]; unfold U CapZone CapIn;fun_prop
   simp_rw [he, readAt]
   let d':= Module.finrank ℂ (F.level d)
   let A:= Module.finBasis ℂ (F.level d)
   let c(k: Fin d')(v: F.level d):=A.repr v k
   have hp k: Continuous (c k):=(A.coord k).continuous_of_finiteDimensional
   let u(i:Fin d')(t:U)(k:Fin (n+n)):ℂ:= Fin.append (fun j:Fin n=> star (c i (t.1.val.2 j.rev))) (fun j:Fin n=> c i (t.2.val.2 j)) k
   let M(i:Fin d'):= Fin.append (fun _:Fin n=> F.adj a (A i).val) (fun _:Fin n=> (A i).val)
   have hc i k: Continuous (fun t=> u i t k):=by
      refine Fin.addCases (fun j=>?_) (fun j=>?_) k
      · simp only [u,Fin.append_left]; apply (continuous_star (R:=ℂ)).comp; exact (hp _).comp (show Continuous (fun t:U=> t.1.val.2 j.rev) by unfold U CapZone CapIn; fun_prop)
      simp only [u,Fin.append_right]; exact (hp _).comp (show Continuous (fun t:U=> t.2.val.2 j) by unfold U CapZone CapIn;fun_prop)
   have b(t:U)(k:Fin (n+n)): h t k=∑ j, u j t k • M j k:=by
      have hy (t:F.level d): (F.level d).subtype t=∑ j: Fin d', c j t • (A j).val:=by
         nth_rw 1 [←A.sum_repr t]; rw [map_sum];simp_rw [map_smul];rfl
      refine Fin.addCases (fun k=>?_) (fun k=>?_) k
      · simp only [h,u,M, Fin.append_left]; change F.adj a ((F.level d).subtype _) = _
        rw [hy,map_sum]; congr 1; ext; rw [LinearEquiv.map_smulₛₗ]; rfl
      simp only [h,u,M,Fin.append_right]; exact hy _
   let e(i: Fin (n+n) → Fin d')(t:U):= ∏ j,u (i j) t j
   have heq(t:U): S _ (z t) (h t)=∑ i: Fin (n+n) → Fin d', e i t * S _ (z t) (fun j=> M (i j) j):=by
      conv_lhs=> rw [funext (b t)]
      rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun j _=> MultilinearMap.map_smul_univ ..
   simp_rw [heq]
   refine continuous_finsetSum _ fun i _=> (show Continuous (e i) from continuous_finsetProd _ (fun j _=>hc _ _)).mul ?_
   exact continuousOn_univ.mp ((p.smooth (n+n) (fun j=> M (i j) j)).continuousOn.comp hZ.continuousOn (fun t _=>hz t))
lemma sample_cont [FiniteDimensional ℂ (F.level d)](p:Fields.Euclidean S): Continuous (C.sample n d):= by
  refine continuous_iff_continuousAt.mpr (fun t=> OS.ketC _ t ?_ ?_)
  · exact ((C.sample_both p).comp (continuous_id.prodMk continuous_id)).continuousAt
  exact ((C.sample_both p).comp (continuous_const.prodMk continuous_id)).continuousAt
lemma samples (E:F.System P): range C.GNS.plant= ⋃ i:ℕ×ℕ, range (C.sample i.1 i.2) :=by
    ext x; constructor
    · rintro ⟨v,rfl⟩
      let l:=v.val
      obtain ⟨d,f,h⟩:=Rotate.cover_cap E (tokens l)
      let q:CapIn F l.length d:=(positions l,f)
      have he : v.val=parcels q:=by
         change l= realize ((F.level d).subtype ∘ f) (positions l); rw [←h,realize]; exact (List.ofFn_get l).symm
      refine mem_iUnion.mpr ⟨(l.length,d),⟨⟨q,he ▸ v.property⟩,?_⟩⟩ -- he dep
      apply congrArg C.GNS.plant; exact Subtype.ext he.symm
    rw [mem_iUnion]; rintro ⟨⟨i,j⟩,z,rfl⟩; exact ⟨_,rfl⟩
lemma separable (E:F.System P)(p:Fields.Euclidean S): SeparableSpace C.H:=by
    have he i:(FiniteDimensional ℂ (F.level i)):=E.finite i
    have hk: IsSeparable (range C.GNS.plant):=by
       rw [samples C E]; apply IsSeparable.iUnion; intro i
       haveI:=he i.2
       haveI : SecondCountableTopology (F.level i.2):= by infer_instance
       exact isSeparable_range (C.sample_cont p)
    rw [← isSeparable_univ_iff,← C.GNS.dense.closure_eq]
    exact hk.span.closure
end Chamber
end YM.Massive.Bridge
