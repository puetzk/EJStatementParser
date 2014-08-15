# -*- coding: utf-8 -*-
import pdfquery
import pyquery
import re
import copy
import datetime
import os
import sys
import argparse
import glob
import itertools
import time
from lxml import etree

# https://pythonhosted.org/pyquery/api.html
# http://www.unixuser.org/~euske/python/pdfminer/programming.html

# future: https://pypi.python.org/pypi/pdfminer3k

def coalesce(*args):
    for arg in args:
        if arg is not None: return arg
    return None


def window_iterator(it, n):
    # Ensure it's an iterator and get the first field
    it = iter(it)

    state = (None,) *n

    for item in it:
        state = state[1:] + (item,)
        yield state

#http://code.activestate.com/recipes/510402-attribute-proxy-forwarding-attribute-access/
class forwardTo(object):
    def __init__(self, objectName, attrName):
        self.objectName = objectName
        self.attrName = attrName
    def __get__(self, instance, owner=None):
        return getattr(getattr(instance, self.objectName), self.attrName)
    def __set__(self, instance, value):
        setattr(getattr(instance, self.objectName), self.attrName, value)
    def __delete__(self, instance):
        delattr(getattr(instance, self.objectName), self.attrName)
        
class Span(object):
    def __init__(self, min = None, max = None, size = None):
        if size is not None:
            if min is None: min = max - size
            elif max is None: max = min + size
            else: raise ValueError("cannot specify both ends and size")
        self.min = min
        self.max = max

    @property
    def size(self): return self.max-self.min

    def __repr__(self):
        return "%f,%f" % (self.min, self.max)

    def __cmp__(self, other):
        if self.max < other.min: return -1
        elif self.min > other.max: return 1
        else: return 0

    def overlaps(self, other, size = 0):
        return (other.max - self.min) >= size and (self.max - other.min) >= size

    def union(self, other):
        return Span(min(self.min, other.min), max(self.max, other.max))

class BBox(object):
    def __init__(self, xy=None,
                 left=None, right=None, top=None, bottom=None, # float
                 width=None, height=None, # float
                 x=None, y=None): #Span or PyQuery
        if xy is not None:
            if width is None:
                if x is None: x = xy
            if height is None:
                if y is None: y = xy

        if isinstance(x, pyquery.PyQuery):  x = Span(float(x.attr('x0')), float(x.attr('x1')))
        if isinstance(y, pyquery.PyQuery):  y = Span(float(y.attr('y0')), float(y.attr('y1')))     

        self.x = Span(left if left is not None else x.min if x is not None else None,
                      right if right is not None else x.max if x is not None else None,
                      width)
        self.y = Span(bottom if bottom is not None else y.min if y is not None else None,
                      top if top is not None else y.max if y is not None else None,
                      height)

    def __repr__(self):
        return "%f,%f,%f,%f" % (self.x.min, self.y.min, self.x.max, self.y.max)

    width = forwardTo('x','size')
    left = forwardTo('x','min')
    right = forwardTo('x','max')

    height = forwardTo('y','size')
    bottom = forwardTo('y','min')
    top = forwardTo('y','max')

    def move(self,dX,dY):
        self.x.min += dX
        self.x.max += dX        
        self.y.min += dY
        self.y.max += dY
        return self

    def expand(self,d=0, dX=None, dY=None, left=None,right=None,top=None,bottom=None):
        self.x.min -= coalesce(left,   dX, d)
        self.y.min -= coalesce(bottom, dY, d)
        self.x.max += coalesce(right,  dX, d)
        self.y.max += coalesce(top,    dY, d)
        return self

class SpanDictionary(object):
    def __init__(self, merge_overlap = True, overlap_size = 1):
        self._items = dict()
        self.merge_overlap = merge_overlap
        self.overlap_size = overlap_size

    def keys_overlaps(self, span):
        keys = [i for i in self._items.iterkeys() if i.overlaps(span, self.overlap_size)]
        if len(keys) > 1 and not self.merge_overlap: #take leftmost
            keys = [ min(keys) ]
        return keys

    def __getitem__(self,span):
        matching_keys = self.keys_overlaps(span)
        if len(matching_keys) == 1:
            return self._items[matching_keys[0]]
        else:
            key = copy.copy(span)
            val = dict()
            for i in matching_keys:
                key = key.union(i)
                val.update(self._items.pop(i))
            self._items[key] = val
            return val
        
    def __delitem__(self,span):
        self._items.__delitem__(span)
        
    def __contains__(self, span):
        return self.keys_overlaps(span).__nonzero__()
             
    def __iter__(self): return self._items.__iter__()
    def __len__(self): return self._items.__len__()
    def __repr__(self): return self._items.__repr__()
    def keys(self, sort = True, reverse = False):
        keys = self._items.keys()
        if sort: keys.sort(reverse = reverse)
        return keys
    def values(self, sort = True, reverse = False): return [self._items[i] for i in self.keys(sort, reverse)]
    def items(self, sort = True, reverse = False):
        items = self._items.items()
        if sort: items.sort(key = lambda x: x[0], reverse = reverse)
        return items

class page_range(object):
    def __init__(self, begin, end = None, **attrfuncs):
        self.begin = begin.parents('LTPage')
        if end:
            self.endpage = end.parents('LTPage')[0]
        else:
            self.endpage = None
        self.attrfuncs = attrfuncs
        for key in attrfuncs.keys():
            setattr(self,key,None)

    def __iter__(self): return self

    def next(self):
        if self.begin:
            self.page = self.begin
            self.begin = None
        else:
            if self.page[0] is self.endpage:
                self.page = None
            else:
                self.page = self.page.next('LTPage')
            
        if not self.page:
            raise StopIteration

        for key, func in self.attrfuncs.items():
            setattr(self, key, func(self.page))
                    
        return self.page

# A generator form of the above
# somewhat shorter, but can't easily store the page/bbox when multiple passes chew on the same next()
#def page_generator(begin, end = None):
#    page = begin.parents('LTPage')
#
#    while page:
#        yield page
#        if end and page[0] is end.parents('LTPage')[0]: break
#        page = page.next('LTPage')
                  
class Statement(object):
    def __init__(self, filename):
        self.filename = filename
        self.pdf = pdfquery.PDFQuery(filename)

    def load(self):
        self.pdf.load()

        account = self.pdf.pq('LTTextLineHorizontal:in_bbox("0,522,288,612"):contains("Account number:")').eq(0)
        page = account.parents('LTPage')
        account_bbox = BBox(account)
        self.account = re.search(r'Account number:\s*([\d-]*)',unpretty(account.text())).group(0)

        date_bbox = copy.copy(account_bbox).move(0,-account_bbox.height * 2).expand(5)
        date = page.find('LTTextLineHorizontal:in_bbox("%s")' % (date_bbox))

        date_matches = re.search(r'^\s*(.+?)\s*-\s*(.+?)\s*$',unpretty(date.text()))
        self.endDate = datetime.datetime.strptime(date_matches.group(2),'%B %d, %Y')
        self.startDate = datetime.datetime.strptime(date_matches.group(1),'%B %d').replace(year = statement.endDate.year)

        self.tables()

    @staticmethod
    def page_content(page):
        page_bbox = BBox(page)
        header = page.find('LTFigure:overlaps_bbox("%s")' % (BBox(x=page_bbox.x, top=page_bbox.top, height=18)))
        footer = page.find('LTFigure:overlaps_bbox("%s")' % (BBox(x=page_bbox.x, bottom=page_bbox.bottom, height=18)))
        content_bbox = BBox(x=page_bbox.x, top = BBox(header).bottom, bottom = BBox(footer).top)
#       content = page.find(':in_bbox("%s")' % (content_bbox))
#        for i in content:
#            print etree.tostring(i, pretty_print=True).encode('utf8')

        return content_bbox

    @staticmethod
    def gridline_span(item):
        page = item.parent('LTPage')
        item_bbox = BBox(item)
        lines = page.find('LTCurve:overlaps_bbox("%s")' % (BBox(x=item_bbox.x, y=page)))
        gutters = [BBox(line).y for line in lines.items()]
        below = max(i for i in gutters if i < item_bbox.y)
        above = min(i for i in gutters if i > item_bbox.y)
        return Span(below.max if below is not None else item_bbox.bottom,
                    above.min if above is not None else item_bbox.top)

    def tables(self):

        def cleanup_regex(item, fields):
            for key,rules in fields.items():
                if key in item:
                    value = item[key]
                    for regex, template, func in rules:
                        match = regex.search(value)
                        if match:
                            value = value[:match.start()] + match.expand(template) + value[match.end():]
                            if func:
                                item.update(func(match))

                    if value:
                        item[key] = value
                    else:
                        del item[key]
        def cleanup_rename(item, mapping):
            for src,dst in mapping.items():
                if src in item:
                    item[dst] = item.pop(src)

        assets = self.pdf.pq('LTTextLineHorizontal:contains("Your Assets at Edward Jones")')
        if assets:
            assets_data = []
            for page in page_range(assets):
                content_bbox = Statement.page_content(page)
                total_assets = page.find('LTTextLineHorizontal:contains("Total estimated asset value")')

                if page[0] is assets.parent('LTPage')[0]:
                    content_bbox.top = BBox(assets).bottom
                if total_assets:
                    content_bbox.bottom = BBox(total_assets).top

                header = page.find('LTTextLineHorizontal:contains("Mutual funds"):in_bbox("%s")' % (BBox(left = content_bbox.left, width=200, y = content_bbox.y)))
                header_y = self.gridline_span(header)
                content_bbox.top = header_y.min

                def cleanup_assets(item):
                    cleanup_rename(item, {'Mutual funds, continued': 'Mutual funds'})

                    cleanup_regex(item, {
                    'Mutual funds':[
                        (re.compile(r'^Quote Symbol:\s*(\w+)$'), '', lambda m: [('Symbol',m.group(1))])
                    ]})

                assets_data += self.parse_table(page, content_bbox, header_y.size, cleanup_assets)
                # found the end, so now we're done
                if total_assets: break

        print "Assets"
        for asset in assets_data:
            print asset

        sections = set()

        summary = self.pdf.pq('LTTextLineHorizontal:contains("Summary of Your Investment Activity")')
        summary_pages = page_range(summary, content_bbox=lambda page: Statement.page_content(page))

        next(summary_pages)
        summary_pages.content_bbox.top = BBox(summary).bottom

        while summary_pages.page:
            detail = summary_pages.page.find('LTTextLineHorizontal:contains("Detail of Your Investment Activity")')
            if detail:
                summary_pages.content_bbox.bottom = BBox(detail).top
                
            if summary_pages.page.find('LTTextLineHorizontal:in_bbox("%s"):contains("Deposits and transfers in")' % (summary_pages.content_bbox)):
                sections.add("Deposits")
            if summary_pages.page.find('LTTextLineHorizontal:in_bbox("%s"):contains("Income")' % (summary_pages.content_bbox)):
                sections.add("Income")            
            if summary_pages.page.find('LTTextLineHorizontal:in_bbox("%s"):contains("Withdrawals to purchase securities")' % (summary_pages.content_bbox)):
                sections.add("Purchases")
            if summary_pages.page.find('LTTextLineHorizontal:in_bbox("%s"):contains("Fees")' % (summary_pages.content_bbox)):
                sections.add("Fees")            
           

            if detail:
                break
            else:
                next(summary_pages)
        

        detail = self.pdf.pq('LTTextLineHorizontal:contains("Detail of Your Investment Activity")')
        detail_pages = page_range(detail, content_bbox=lambda page: Statement.page_content(page))

        next(detail_pages)
        detail_pages.content_bbox.top = BBox(detail).bottom
        
        if "Deposits" in sections:
            def cleanup_deposits(item):
                 cleanup_rename(item, {0:'Description'})
                 cleanup_regex(item,{
                    'Description': [
                        (re.compile('^(ELECTRONIC TRANSFER FROM)\s*'),'', lambda m: [('Activity',m.group(1))])
                    ]})
            deposits_data = self.table_data(detail_pages,'Deposits and transfers in','Total deposits and transfers in', cleanup_deposits)
            for deposit in deposits_data:
                print deposit

        if "Income" in sections: # income is not always present, see if it's even in the document at all
            print "Income"
            
            def cleanup_income(item):
                cleanup_rename(item, {0:'Description'})
                
            income_data = self.table_data(detail_pages,'Income','Total income', cleanup_income)
            for income in income_data:
                print income


        if "Purchases" in sections:
            print "Purchase"

            def cleanup_purchase(item):
                cleanup_rename(item, {0:'Description'})
                
                delim = r'(?:\s*;\s*)?'
                cleanup_regex(item,{
                    'Description': [
                        (re.compile(r'^(REINVESTMENT INTO|SYSTEMATIC INVESTMENT PLAN)\s*'),'', lambda m: [('Activity',m.group(1))]),
                        (re.compile(r'(\$[\d,]+)\s+BREAKPT' + delim),'', lambda m: [('BREAKPT',m.group(1))]),
                        (re.compile(r'([\d.]+%)\s+CHRG' + delim),'', lambda m: [('Front Load',m.group(1))])
                    ]})

            purchase_data = self.table_data(detail_pages, 'Withdrawals to purchase securities','Total withdrawals to purchase securities', cleanup_purchase)

            for purchase in purchase_data:
                print purchase

        #FIXME: Fees shares headers with Purchases (between the "Subtraction" and whatever comes next), it does't have its own
        if "Fees" in sections:
            print "Fees"

            def cleanup_fees(item):
                cleanup_rename(item, {0:'Description'})
            
            fee_data = self.table_data(detail_pages, 'Fees','Total fees', cleanup_fees)

            for fee in fee_data:
                print fee
    @staticmethod
    def table_data(page_range, title_text, total_text, cleanup = None):
        data = []
        while page_range.page:
            title = page_range.page.find('LTTextLineHorizontal:in_bbox("%s"):contains("%s")' % (page_range.content_bbox, title_text))
            if not title: # keep searching on the next page
                next(page_range)
                continue
            
            title_bbox = BBox(title)
            
            cell_bbox = BBox(left = title_bbox.right, right = page_range.content_bbox.right, top = title_bbox.top, bottom = page_range.content_bbox.bottom)

            total = page_range.page.find('LTTextLineHorizontal:in_bbox("%s"):contains("%s")' % (page_range.content_bbox, total_text))
            if total:
                cell_bbox.bottom = BBox(total).top

            line = page_range.page.find('LTCurve:overlaps_bbox("%s")' % (BBox(x = title_bbox.x, bottom = title_bbox.top, height = 8)))
            if line:
                cell_bbox.top = BBox(line).bottom

            data += Statement.parse_table(page_range.page, cell_bbox, 3*title_bbox.height, cleanup)

            # found the end, so mark what we consumed and return
            if total:
                page_range.content_bbox.top = cell_bbox.bottom
                break;
            else:
                next(page_range)
        return data

    @staticmethod
    def parse_table(page, cell_bbox, height=20, cleanup = None):
        rows = Statement.parse_rows(page, cell_bbox, height=height)
        if cleanup:
            for i in rows.values():
                cleanup(i)
        rows = Statement.merge_by_lines(rows, page, cell_bbox)
        # PDF origin is *bottom*-left, so reverse the sort
        return rows.values(sort = True, reverse = True)

    #FIXME: merge_by_lines is still missing some merges...
    @staticmethod
    def merge_by_lines(rows, page, cell_bbox):        
        lines = page.find('LTCurve:overlaps_bbox("%s")' % (cell_bbox))

        gutters = [BBox(line).y for line in lines.items()]
        gutters.sort()
                
        multirows = SpanDictionary(merge_overlap = False)
        for below,above in window_iterator(gutters,2):
            span = Span(cell_bbox.bottom if below is None else below.max, cell_bbox.top if above is None else above.min)
            multirows[span].update(dict())

        for span, data in rows.items(reverse=True):
            target = multirows[span]
            for key,value in data.items():
                if key in target:
                    target[key] += '\n' + value
                else:
                    target[key] = value
                    
        for span, data in multirows.items():
            if not data:
                del multirows[span]
        return multirows

    @staticmethod
    def parse_rows(page, cell_bbox, height=20):
        columns = SpanDictionary(merge_overlap = False)

        # LTTextBoxHorizontal sometimes merges too much (across gridlines), but LTTextLineHorizontal doesn't merge multiline values
        # So this has to be done manually anyway...
        headers = page.find('LTTextLineHorizontal:in_bbox("%s")' % (BBox(x = cell_bbox.x, bottom = cell_bbox.top, height = height)))
        for header in sorted(headers.items(), key = lambda x: BBox(x).y):
            column = columns[BBox(header).x]
            if 'title' in column:
                column['title'] += '\n' + header.text()
            else:
                column['title'] = header.text()

        #for i in headers:
         #   print etree.tostring(i, pretty_print=True).encode('utf8')
                    
        rows = SpanDictionary(merge_overlap = True)

        unknown_column = 0

        cells = page.find('LTTextLineHorizontal:in_bbox("%s")' % (cell_bbox))
        for cell in cells.items():
            cell_bbox = BBox(cell)

            if cell.text(): #TODO where are these LTTextLineHorizontal items with no text coming from?
                row = rows[cell_bbox.y]
                column = columns[cell_bbox.x]
                if not 'title' in column:
                    column['title'] = unknown_column
                    unknown_column += 1
                row[column['title']] = cell.text()

        return rows
        
    def __str__(self):
        return "Statement for %s, %s to %s" % (self.account, self.startDate, self.endDate)
    
def unpretty(s):
    return s.replace(u'−','-')

parser = argparse.ArgumentParser(description='Scan EJ Statement PDFs.')
parser.add_argument('infiles', nargs='*')

globbed_argv = itertools.chain.from_iterable(glob.iglob(x) for x in sys.argv[1:])
args = parser.parse_args(globbed_argv)

for file in args.infiles:
    print "parsing %s" % (file)
    statement = Statement(file)
    statement.load()
    timestamp = time.mktime(statement.endDate.utctimetuple())
    os.utime(statement.filename, (timestamp,timestamp))
    print statement
