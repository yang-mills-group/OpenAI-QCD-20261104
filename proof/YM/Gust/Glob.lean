import YM.Gust.Valley
set_option maxHeartbeats 790000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Analysis Function Set Filter MeasureTheory Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix Classical
variable {K:Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T){m n:ℕ}
abbrev Gala(T:Pollens P K)(n:ℕ):= List (E4 × Mater T n)
namespace Gala
abbrev purse (v:Gala T n):= led (v.map fun p=>p.2.u)
abbrev Piers (v:Gala T n):= (v.map Prod.fst).Nodup
noncomputable abbrev wall (v:Gala T n)(i:Fin (n+1)) : Strip K:= v.map fun ⟨x,j⟩=>(x,j.v i)
noncomputable def gate (v:Gala T n):ℂ:= purse v*∏ i:Fin (n+1), Strip.tone (wall v i)
variable (v w p:Gala T n)
noncomputable abbrev xpos(v:Gala T n):Points v.length:=points fun i=> (v.get i).1
lemma alignment : gate v= ValueP (xpos v) (fun i=> (v.get i).2):=by
       unfold ValueP gate purse; rw [show List.ofFn (fun i=>(v.get i).2.u)= (v.map fun p=>p.2.u) from ?_] -- dangerous
       exact congr_arg ( (led _) * · ) (Finset.prod_congr rfl (fun j _=> introduces Prod.fst (fun x=>x.2.v j) v)) -- order
       rw [show (fun i=>(v.get i).2.u)=(fun p:E4 ×Mater T n=>p.2.u)∘ v.get from rfl,←List.map_ofFn,List.ofFn_get]
abbrev stageP (u: Fin m→Mater T n)(x:Points m): Gala T n:= List.ofFn fun i=>(x i,u i)
lemma fit (u:Fin m→ Mater T n)(x:Points m) : gate (stageP u x)= ValueP x u:=by
       have he : ∀ n' m':ℕ,∀ (h:n'=m')(p:Points n')(q:Points m')(x: Fin n'→Mater T n)(y:Fin m'→Mater T n), (∀ i,p i=q (Fin.cast h i))→(∀ i,x i=y (Fin.cast h i))→ ValueP p x=ValueP q y:=by
            intro n m h; subst m; intro p q x y h k; simp only[Fin.cast_refl,id_eq] at h k; rw [PiLp.ext h,funext k]
       rw [alignment]; refine he _ _ (by simp[stageP]) _ _ _ _ ?_ ?_ <;> intro i <;> simp[xpos,stageP]<;>rfl -- ???
lemma pier(v:Gala T n): Piers v ↔ xpos v∈conf _:=by
      rw [Piers, show v.map Prod.fst=List.ofFn (fun i=> (v.get i).1) from ?_,List.nodup_ofFn]; rfl
      rw [show (fun i=> (v.get i).1)=Prod.fst ∘v.get from rfl,←List.map_ofFn,List.ofFn_get]
lemma length_ok (s:Gala T n)(hs:Piers s)(i) : Strip.distinct (wall s i):=(Strip.spots _).mpr (by simpa only[Piers,wall,List.map_map,Function.comp_def] using hs)
variable (x y:E4× Mater T n)
lemma meMem (v:Mater T n)(i): markedW T (Kind.q v.u i) (v.v i):=by
       change T.parity (v.v i)= _; rw [(hue ..).1 (v.mem i)]; cases h:q v.u i<;>simp[tauMod]
open Finset
abbrev swp (a b:Kind n)(i:Fin (n+1)):ℂ:= if Kind.q a i && Kind.q b i then -1 else 1
lemma roll_s (p q: Kind n):bit p q * ∏ i:Fin (n+1),swp p q i= bit q p:=by
       unfold swp; cases p with
       | none=> cases q <;> simp[Fin.prod_univ_succ,bit, Kind.q]
       | some p=>
         rcases q with _|q; · simp[Fin.prod_univ_succ,bit,Kind.q]
         rw[Fin.prod_univ_succ,prod_eq_single_of_mem p (Finset.mem_univ p)]
         · rcases lt_trichotomy p q with h|h|h; simp [bit,Kind.q,h, lt_asymm h,h.ne]; simp [h, Kind.q,bit]; simp [bit,Kind.q,h,lt_asymm h,Ne.symm h.ne]
         · intro i _ h; simp [Kind.q,h]
include hf
lemma swayM(h:Piers (v++x::y::w)):gate (v++x::y::w)=gate (v++y::x::w):=by
      have hZ(i:Fin (n+1)):tone (wall (v++x::y::w) i)= swp x.2.u y.2.u i*tone (wall (v++y::x::w) i):=by
          have hv:Piers _:=h; have he:=length_ok _ h i; simp only [wall,List.map_append,List.map_cons] at *; exact hf.flips _ _ _ _ _ _ he (meMem ..) (meMem ..)
      simp_rw [gate,hZ]; rw [prod_mul_distrib,← mul_assoc]; congr 1; unfold purse; simp_rw [List.map_append,List.map_cons]; rw [turnL,turnL]; simp only [led, lead_cons];
      let f : E4 × Mater T n→Kind n:=fun i=>i.2.u; let A:=v.map f; let B:=w.map f
      have he : Kind.cross A (x.2.u:: y.2.u:: B)= Kind.cross A (y.2.u:: x.2.u:: B):=by
           apply Kind.cross_sel; intro i; unfold turnW; exact (List.Perm.map _ (List.Perm.swap _ _ _)).prod_eq -- order
      rw[he]; linear_combination Kind.cross A (y.2.u::x.2.u::B)*led A*lead x.2.u B* lead y.2.u B*led B * (roll_s x.2.u y.2.u)
lemma market {l v:Gala T n}(h:l.Perm v):∀ (a:Gala T n), Piers (a++l)→ gate (a++l)=gate (a++v):=by
      induction h with
      | nil=> exact fun _ _=>rfl
      | @cons x i j h ih=> intro a hx; simpa [List.append_assoc] using ih (a++[x]) (by simpa [List.append_assoc] using hx)
      | @swap x y l=>exact fun i hh=> swayM hf i _ _ _ hh
      | @trans a b c h v he hv=> intro i hh; exact (he i hh).trans (hv i (List.Perm.nodup ((h.append_left i).map Prod.fst) hh))
lemma kiosks (h:v.Perm w)(hp:Piers v):gate v=gate w:=by simpa only [List.nil_append] using market hf h [] (List.nil_append v |>.symm ▸ hp : Piers ([]++v))
end Gala
end YM.Massive.Gust
#print axioms YM.Massive.Gust.Gala.kiosks
