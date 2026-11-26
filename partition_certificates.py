#!/usr/bin/env python3
"""Partition generated exact certificates into bounded independent Lean jobs."""
import argparse,json,re
from pathlib import Path

END='end LeanVerification.PositiveDCompletion\n'
HEADER='''noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

'''

def decls(text):
    starts=list(re.finditer(r'^(def|theorem) (\w+)',text,re.M))
    stop=text.rfind('end LeanVerification.PositiveDCompletion')
    return [(m.group(1),m.group(2),text[m.start():starts[k+1].start() if k+1<len(starts) else stop].strip()+'\n\n') for k,m in enumerate(starts)]


def write(out,name,imports,body):
    (out/(name+'.lean')).write_text(''.join(f'import LeanVerification.PositiveDCompletion.{i}\n' for i in imports)+'\n'+HEADER+body+END)


def polynomial(out,name):
    text=(out/(name+'.lean')).read_text();ds=decls(text)
    if not any(k=='def' for k,n,v in ds):raise ValueError(f'{name} is already partitioned; regenerate first')
    data=name+'Data';dep='CertificateCoordinates' if name.startswith('Upper') else 'LowerCoordinates'
    write(out,data,[dep],''.join(v for k,n,v in ds if k=='def'))
    parts=[];final=[]
    for k,n,v in ds:
        if k!='theorem':continue
        if name.startswith('Upper') and n==name.replace('UpperPolynomial','upperNum')+'_map':final.append(v);continue
        part=name+('Clear' if n.endswith('_clear') else 'Map'+re.search(r'Coeff(\d+)_map',n).group(1))
        write(out,part,[data],v);parts.append(part)
    write(out,name,parts,''.join(final))
    return [data]+parts+[name]


def certificate(out,name):
    text=(out/(name+'.lean')).read_text();ds=decls(text)
    if not any(k=='def' for k,n,v in ds):raise ValueError(f'{name} is already partitioned; regenerate first')
    poly=name.replace('Certificate','Polynomial');data=name+'Data'
    body=''.join(v for k,n,v in ds if k=='def' or ('Weight' in n and k=='theorem'))
    write(out,data,[poly],body)
    blockgroups={};coeffs=[];final=[]
    for k,n,v in ds:
        if k!='theorem' or 'Weight' in n:continue
        if 'Block' in n:
            i=int(re.search(r'Block(\d+)',n).group(1));blockgroups.setdefault(i//5,[]).append(v)
        elif 'Coeff' in n:
            i=int(re.search(r'Coeff(\d+)',n).group(1));part=name+'Coefficient'+str(i)
            write(out,part,[data],v);coeffs.append(part)
        else:final.append(v)
    blocks=[]
    for i,values in sorted(blockgroups.items()):
        part=name+f'Blocks{i:02d}';write(out,part,[data],''.join(values));blocks.append(part)
    write(out,name,blocks+coeffs,''.join(final))
    return [data]+blocks+coeffs+[name]


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
    p.add_argument('names',nargs='+');p.add_argument('--order',type=Path)
    args=p.parse_args();order=[]
    for name in args.names:
        order.extend(polynomial(args.directory,name) if 'Polynomial' in name else certificate(args.directory,name))
    if args.order:args.order.write_text(json.dumps(order,indent=2)+'\n')
    for n in order:print(n)


if __name__=='__main__':main()
